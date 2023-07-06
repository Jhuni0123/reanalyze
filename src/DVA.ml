open CL.Typedtree
open CL.Types

exception RuntimeError of string

module Current = struct
  let cmtModName : string ref = ref ""
end

module Id = struct
  (* Ident.t is unique under a module file, except for the ident of top-level module (persistent). *)
  (* Then Ident.t with top-level module name is unique for whole codebase. *)
  type t = string * CL.Ident.t

  let create ctx ident : t = (ctx, ident)

  let createCmtModuleId modname : t =
    ("+", {name = modname; stamp = 0; flags = 0})

  let ident (id : t) = snd id
  let ctx (id : t) = fst id
  let name id = id |> ident |> CL.Ident.name
  let hash id = CL.Ident.hash (snd id)

  let compare a b =
    let c = String.compare (ctx a) (ctx b) in
    if c <> 0 then c else CL.Ident.compare (ident a) (ident b)

  let equal a b =
    String.equal (ctx a) (ctx b) && CL.Ident.equal (ident a) (ident b)

  let print (id : t) =
    Printf.printf "[%s]%s#%d" (ctx id) (name id) (ident id).stamp
end

module IdTbl = Hashtbl.Make (Id)
module IdSet = Set.Make (Id)


type label = string * int
type var = Val of label | SideEff of label
type arg = label option list

type memory_label = string * int

type ctor =
  | Variant of string
  | Construct of constructor_description
  | Record
  | Tuple
  | Member of string
  | Array

type fld = ctor * int option

type case = {
  pat: pattern;
  guard: var option;
  expr: var;
}

type se =
  (* Set variable *)
  | Var of var
  | Id of Id.t
  (* Value *)
  | Unknown
  | Mem of memory_label
  | Prim of CL.Primitive.description
  | Fn of label * label list
  | App of label * arg
  | PrimApp of CL.Primitive.description * arg
  | Ctor of ctor * label list
  | Fld of label * fld
  (* Side Effect *)
  | SideEffect
  | AppliedToUnknown

module SESet = Set.Make(struct
  type t = se
  let compare = compare
end)

let address_tbl : (string, int) Hashtbl.t = Hashtbl.create 10

let new_memory mod_name : memory_label =
  let label =
    match Hashtbl.find_opt address_tbl mod_name with
    | None ->
      Hashtbl.add address_tbl mod_name 0;
      0
    | Some label' ->
      Hashtbl.replace address_tbl mod_name (label' + 1);
      label' + 1
  in
  (mod_name, label)

module Worklist = struct
  type t = SESet.t ref

  let add x (worklist : t) = worklist := SESet.add x !worklist
  let mem x (worklist : t) = SESet.mem x !worklist

  let prepare_step (worklist : t) (prev_worklist : t) =
    prev_worklist := !worklist;
    worklist := SESet.empty
end

let worklist : Worklist.t = ref SESet.empty
let prev_worklist : Worklist.t = ref SESet.empty
let sc : (se, SESet.t) Hashtbl.t = Hashtbl.create 256
let reverse_sc : (se, SESet.t) Hashtbl.t = Hashtbl.create 256
let changed = ref false

module Expr = struct
  type label = string * int
  type value_expr_summary = {
    exp_type : CL.Types.type_expr;
    exp_loc : CL.Location.t;
    exp_context : string;
  }
  type module_expr_summary = {
    mod_type : CL.Types.module_type;
    mod_loc : CL.Location.t;
    mod_context : string;
  }
  type summary =
    | ValueExpr of value_expr_summary
    | ModExpr of module_expr_summary
    | Tmp

  let label_to_summary : (label, summary) Hashtbl.t = Hashtbl.create 10
  let summary_from_label label = Hashtbl.find label_to_summary label

  let label_tbl = Hashtbl.create 10

  let new_label mod_name : label =
    let num =
      match Hashtbl.find_opt label_tbl mod_name with
      | None ->
        Hashtbl.add label_tbl mod_name 0;
        0
      | Some label' ->
        Hashtbl.replace label_tbl mod_name (label' + 1);
        label' + 1
    in
    (mod_name, num)

  let new_loc label : CL.Location.t =
    let (mod_name, num) = label in
    let loc : Lexing.position = {
      pos_fname = mod_name;
      pos_lnum = num;
      pos_bol = 0;
      pos_cnum = -1;
    } in
    { loc_start = loc; loc_end = loc; loc_ghost = true }

  let preprocess_expression (e: expression) = 
    let label = new_label !Current.cmtModName in
    Hashtbl.add label_to_summary label (ValueExpr {
      exp_type = e.exp_type;
      exp_loc = e.exp_loc;
      exp_context = !Current.cmtModName;
    });
    {e with exp_loc = new_loc label}

  let expression_to_label (e: expression) =
    let pos = e.exp_loc.loc_start in
    (pos.pos_fname, pos.pos_lnum)

  let preprocess_module_expr (me: module_expr) = 
    let label = new_label !Current.cmtModName in
    Hashtbl.add label_to_summary label (ModExpr {
      mod_type = me.mod_type;
      mod_loc = me.mod_loc;
      mod_context = !Current.cmtModName;
    });
    {me with mod_loc = new_loc label}

  let module_expr_to_label (me: module_expr) =
    let pos = me.mod_loc.loc_start in
    (pos.pos_fname, pos.pos_lnum)

  let new_temp () =
    let label = new_label !Current.cmtModName in
    Hashtbl.add label_to_summary label Tmp;
    label
end

let string_of_loc (loc : CL.Location.t) =
  let file, line, startchar = CL.Location.get_pos_info loc.loc_start in
  let filename = file |> String.split_on_char '/' |> List.rev |> List.hd in
  let startchar = startchar + 1 in
  let endchar = loc.loc_end.pos_cnum - loc.loc_start.pos_cnum + startchar in
  Printf.sprintf "%s:%i:%i:%i:%B" filename line (startchar - 1) (endchar - 1)
    loc.loc_ghost

let rec isUnitType (t : type_expr) =
  match t.desc with
  | Tconstr (path, [], _) -> CL.Path.name path = "unit"
  | Tlink t -> isUnitType t
  | _ -> false

let rec isEmptyPropsType (t : type_expr) =
  match t.desc with
  | Tconstr (path, [], _) -> CL.Path.name path = "props"
  | Tlink t -> isEmptyPropsType t
  | _ -> false

module Field = struct
  type t = F_Record of string | F_Tuple of int

  let compare = compare
end

module StringMap = Map.Make (String)

module CstrMap = Map.Make (struct
  type t = constructor_description

  let compare = compare
end)

module FieldMap = Map.Make (Field)

module Live = struct
  type t =
    | Top
    | Bot
    | Construct of t list CstrMap.t
    | Variant of t option StringMap.t
    | Record of t FieldMap.t

  let variant lbl l : t = Variant (StringMap.singleton lbl l)
  let field f l : t = Record (FieldMap.singleton f l)
  let construct cstr ls : t = Construct (CstrMap.singleton cstr ls)

  let constructi cstr idx l : t =
    let ls = List.init (idx + 1) (function i when i = idx -> l | _ -> Bot) in
    Construct (CstrMap.singleton cstr ls)

  let rec join a b =
    match (a, b) with
    | Top, _ | _, Top -> Top
    | Bot, x | x, Bot -> x
    | Variant ks, Variant ks' ->
      let join_opt ao bo =
        match (ao, bo) with
        | Some a, Some b -> join a b
        | Some a, None -> a
        | None, Some b -> b
        | None, None -> Bot
      in
      Variant
        (StringMap.union (fun k l1 l2 -> Some (Some (join_opt l1 l2))) ks ks')
    | Record fs, Record fs' ->
      Record (FieldMap.union (fun k l1 l2 -> Some (join l1 l2)) fs fs')
    | Construct cs, Construct cs' ->
      let rec join_list l1 l2 =
        match (l1, l2) with
        | [], [] -> []
        | [], _ -> l2
        | _, [] -> l1
        | hd1 :: tl1, hd2 :: tl2 -> join hd1 hd2 :: join_list tl1 tl2
      in
      Construct (CstrMap.union (fun k l1 l2 -> Some (join_list l1 l2)) cs cs')
    | _ -> Top

  let rec meet a b =
    match (a, b) with
    | Top, x | x, Top -> x
    | Bot, _ | _, Bot -> Bot
    | Variant ks, Variant ks' ->
      let meet_opt ao bo =
        match (ao, bo) with Some a, Some b -> meet a b | _ -> Bot
      in
      Variant
        (StringMap.merge
           (fun k op1 op2 ->
             match (op1, op2) with
             | Some l1, Some l2 -> Some (Some (meet_opt l1 l2))
             | _ -> None)
           ks ks')
    | Record fs, Record fs' ->
      Record
        (FieldMap.merge
           (fun k op1 op2 ->
             match (op1, op2) with
             | Some l1, Some l2 -> Some (meet l1 l2)
             | _ -> None)
           fs fs')
    | Construct cs, Construct cs' ->
      let rec meet_list l1 l2 =
        match (l1, l2) with
        | hd1 :: tl1, hd2 :: tl2 -> meet hd1 hd2 :: meet_list tl1 tl2
        | _ -> []
      in
      Construct
        (CstrMap.merge
           (fun k op1 op2 ->
             match (op1, op2) with
             | Some l1, Some l2 -> Some (meet_list l1 l2)
             | _ -> None)
           cs cs')
    | _ -> Bot

  let variant_inv k l =
    match l with
    | Top -> Top
    | Bot -> Bot
    | Variant ks -> (
      match StringMap.find_opt k ks with
      | None -> Bot
      | Some (Some l) -> l
      | Some None -> Bot)
    | _ -> Bot

  let field_inv k l =
    match l with
    | Top -> Top
    | Bot -> Bot
    | Record fs -> (
      match FieldMap.find_opt k fs with None -> Bot | Some l -> l)
    | _ -> Bot

  let construct_inv cstr_desc idx l =
    match l with
    | Top -> Top
    | Bot -> Bot
    | Construct cs -> (
      match CstrMap.find_opt cstr_desc cs with
      | None -> Bot
      | Some ls -> List.nth_opt ls idx |> Option.value ~default:Bot)
    | _ -> Bot

  let rec equal l1 l2 =
    match (l1, l2) with
    | Top, Top -> true
    | Bot, Bot -> true
    | Variant ks1, Variant ks2 -> StringMap.equal (Option.equal equal) ks1 ks2
    | Record fs1, Record fs2 -> FieldMap.equal equal fs1 fs2
    | Construct cs1, Construct cs2 -> CstrMap.equal (List.equal equal) cs1 cs2
    | _ -> false

  let rec print l =
    let ps = print_string in
    match l with
    | Top -> ps "⊤"
    | Bot -> ps "⊥"
    | Variant ks ->
      ks |> StringMap.bindings
      |> Print.print_list
           (fun (k, vo) ->
             ps "Variant:";
             ps k;
             ps "(";
             (match vo with Some v -> print v | None -> ());
             ps ")")
           "+"
    | Record fs ->
      fs |> FieldMap.bindings
      |> Print.print_list
           (fun (k, v) ->
             ps "Field:";
             (match k with
             | Field.F_Tuple n -> print_int n
             | F_Record f -> print_string f);
             ps "(";
             print v;
             ps ")")
           "*"
    | Construct cs ->
      cs |> CstrMap.bindings
      |> Print.print_list
           (fun (cstr_desc, v) ->
             ps "Cstr:";
             ps cstr_desc.cstr_name;
             ps "(";
             v |> Print.print_list print ",";
             ps ")")
           "+"

  let rec controlledByPat pat =
    match pat.pat_desc with
    | Tpat_any -> Bot
    | Tpat_var _ -> Bot
    | Tpat_alias (pat, id, l) -> controlledByPat pat
    | Tpat_constant c -> Top
    | Tpat_tuple pats ->
      pats
      |> List.mapi (fun i pat -> field (F_Tuple i) (controlledByPat pat))
      |> List.fold_left (fun acc l -> join acc l) Bot
    | Tpat_construct (lid, cstr_desc, pats) ->
      pats |> List.map controlledByPat |> construct cstr_desc
    | Tpat_variant (label, pato, row) ->
      variant label (pato |> Option.map controlledByPat)
    | Tpat_record (fields, closed_flag) ->
      fields
      |> List.map (fun (lid, lbl_desc, pat) ->
             field (F_Record lbl_desc.lbl_name) (controlledByPat pat))
      |> List.fold_left join Bot
    | Tpat_array _ -> Top (* TODO: array *)
    | Tpat_or (pat1, pat2, _) ->
      join (controlledByPat pat1) (controlledByPat pat2)
    | Tpat_lazy _ -> Top
end



module PrintSE = struct
  module Loc = struct
    type t = var

    let compare = compare
  end

  module LocSet = Set.Make (Loc)

  let to_be_explained = ref LocSet.empty

  let print_list print_elem sep l =
    let rec _print_list l =
      match l with
      | [] -> ()
      | [hd] ->
          prerr_string "(";
          print_elem hd;
          prerr_string ")"
      | hd :: tl ->
          prerr_string "(";
          print_elem hd;
          prerr_string ")";
          prerr_string sep;
          _print_list tl;
    in
    prerr_string "[";
    _print_list l;
    prerr_string "]"

  let print_code_loc loc =
    CL.Location.print_loc Format.str_formatter loc;
    prerr_string (Format.flush_str_formatter ())

  let print_summary label =
    let (modname, i) = label in
    match Expr.summary_from_label label with
    | ValueExpr e -> print_code_loc e.exp_loc
    | ModExpr m -> print_code_loc m.mod_loc
    | Tmp -> prerr_string ("temp_" ^ modname ^ "_" ^ string_of_int i)
    (* | exception Not_found -> prerr_string ("label?_" ^ modname ^ "_" ^ string_of_int i) *)

  let print_var = function
    | Val label -> prerr_string "Val ("; print_summary label; prerr_string ")"
    | SideEff label -> prerr_string "Val ("; print_summary label; prerr_string ")"

  let print_param = function
    | None -> ()
    | Some (x, _) -> prerr_string (CL.Ident.name x)

  let print_ctor = function
    | Variant k -> prerr_string k
    | Construct cstr_desc -> prerr_string cstr_desc.cstr_name
    | Record -> prerr_string "Record"
    | Tuple -> prerr_string "Tuple"
    | Member name -> prerr_string name
    | Array -> prerr_string "Array"

  let print_arg = function
    | None -> prerr_string "-"
    | Some a -> print_summary a

  let rec print_se : se -> unit = function
    | Unknown -> prerr_string "⊤"
    | Fn (p, list) ->
      prerr_string "λ";
      print_summary p;
      prerr_string ".";
      print_list print_summary ";" list
    | Prim {prim_name} -> prerr_string ("Prim (" ^ prim_name ^ ")")
    | Var e ->
      prerr_string "Var (";
      print_var e;
      prerr_string ")"
    | PrimApp ({prim_name}, list) ->
      prerr_string "PrimApp (";
      prerr_string prim_name;
      prerr_string ", ";
      print_list print_arg ";" list;
      prerr_string ")"
    | App (e, list) ->
      prerr_string "App (";
      print_summary e;
      prerr_string ", ";
      print_list print_arg ";" list;
      prerr_string ")"
    | Ctor (k, arr) ->
      prerr_string "Ctor (";
      print_ctor k;
      prerr_string ", ";
      let print_mem mem =
        prerr_string "ℓ_";
        prerr_int (snd mem);
      in
      print_list print_mem ";" arr;
      print_list_with_separator arr ";";
      prerr_string ")"
    | Fld (e, lbl) ->
      prerr_string "Fld (";
      print_summary e;
      prerr_string ", (";
      (match lbl with
      | ctor, Some i ->
        print_ctor ctor;
        prerr_string ", ";
        prerr_int i
      | _, None -> prerr_string " , ");
      prerr_string "))"
    | Mem (_, i) -> prerr_string ("!ℓ_" ^ string_of_int i)
    | Id x -> prerr_string (CL.Ident.unique_name (Id.ident x))
    | SideEffect -> prerr_string "φ"

  and print_ses (xs : se list) =
    prerr_string "[";
    List.iter print_se xs;
    prerr_string "]"

  and print_option_list_with_separator l sep =
    let l' = ref l in
    prerr_string "[";
    while !l' <> [] do
      match !l' with
      | Some hd :: tl ->
        prerr_string "(";
        print_summary hd;
        prerr_string ")";
        if tl <> [] then prerr_string sep;
        l' := tl
      | None :: tl ->
        if tl <> [] then prerr_string sep;
        l' := tl
      | _ -> assert false
    done;
    prerr_string "]"

  and print_list_with_separator l sep =
    let l' = ref l in
    prerr_string "[";
    while !l' <> [] do
      match !l' with
      | hd :: tl ->
        prerr_string "ℓ_";
        prerr_int (snd hd);
        if tl <> [] then prerr_string sep;
        l' := tl
      | _ -> assert false
    done;
    prerr_string "]"

  let show_se_with_separator set sep =
    SESet.iter
      (fun x ->
        prerr_string sep;
        print_se x;
        prerr_newline ())
      set

  let show_sc_tbl (tbl : (se, SESet.t) Hashtbl.t) =
    Hashtbl.iter
      (fun key data ->
        if SESet.is_empty data then ()
        else (
          prerr_string "sc :\n";
          print_se key;
          (match key with
          | Fld (_, _) -> prerr_string " <- "
          | _ -> prerr_string " = ");
          prerr_newline ();
          show_se_with_separator data "\t";
          prerr_newline ()))
      tbl

  let filter_closure = function
    | Fn (_, _) | App (_, None :: _) | PrimApp _ | Prim _ -> true
    | _ -> false

  let show_closure_analysis tbl =
    prerr_endline "Closure analysis:";
    Hashtbl.iter
      (fun key data ->
        let set = SESet.filter filter_closure data in
        if SESet.is_empty set then ()
        else (
          print_se key;
          prerr_newline ();
          show_se_with_separator set "\t";
          prerr_newline ()))
      tbl

  let print_sc_info () =
    show_sc_tbl sc

  let print_closure () =
    Format.flush_str_formatter () |> ignore;
    show_closure_analysis sc
end

let lookup_sc se = try Hashtbl.find sc se with Not_found -> SESet.singleton Unknown

exception Escape
let update_worklist key set =
  let summarize elt =
    let idx =
      match elt with
      | App (e, (Some _ :: _ | []))
      | Fld (e, _) ->
        Worklist.add (Var (Val e)) worklist;
        Var (Val e)
      | Var _ | Mem _ | Id _ ->
        Worklist.add elt worklist;
        elt
      | _ -> Worklist.add elt worklist; elt
      (* | _ -> raise Escape *)
    in
    match Hashtbl.find_opt reverse_sc idx with
    | None -> Hashtbl.add reverse_sc idx (SESet.singleton key)
    | Some orig -> Hashtbl.replace reverse_sc idx (SESet.add key orig)
  in
  match key with
  | Mem _ | Id _ ->
    Worklist.add key worklist;
    SESet.iter (fun se -> try summarize se with Escape -> ()) set
  | Var _ ->
    Worklist.add key worklist;
    SESet.iter (fun se -> try summarize se with Escape -> ()) set
  | Fld (e, _) -> summarize (Var (Val e))
  | AppliedToUnknown ->
    Worklist.add key worklist;
    SESet.iter (fun se -> try summarize se with Escape -> ()) set
  | _ -> failwith "Invalid LHS"

let update_sc lhs added =
  let original = lookup_sc lhs in
  let diff = SESet.diff added original in
  if not (SESet.is_empty diff) then (
    changed := true;
    update_worklist lhs diff;
    Hashtbl.replace sc lhs (SESet.union original diff))


(* enforce data to be nonempty *)
let init_sc lhs data =
  (* if data = [] then () *)
  (* else *)
    let set = SESet.of_list data in
    update_worklist lhs set;
    match Hashtbl.find sc lhs with
    | exception Not_found -> Hashtbl.add sc lhs set
    | original -> Hashtbl.replace sc lhs (SESet.union original set)

let annotatedAsLive attributes =
  attributes
  |> Annotation.getAttributePayload (( = ) DeadCommon.liveAnnotation)
  <> None

let rec label_of_path = function
  | CL.Path.Papply (_f, _x) ->
    raise (RuntimeError "I don't know what Papply do.")
    (* let f = label_of_path f in *)
    (* let x = label_of_path x in *)
    (* let temp = Expr.new_temp () in *)
    (* init_sc (Var (Val temp)) [App (f, [Some x])]; *)
    (* temp *)
  | CL.Path.Pdot (x, fld, _) ->
    let x = label_of_path x in
    let temp = Expr.new_temp () in
    init_sc (Var (Val temp)) [Fld (x, (Member fld, Some 0))];
    temp
  | CL.Path.Pident x ->
    let temp = Expr.new_temp () in
    init_sc (Var (Val temp)) [Id (Id.create !Current.cmtModName x)];
    temp

let label_of_expression e = Expr.expression_to_label e
let label_of_module_expr me = Expr.module_expr_to_label me

let rec solve_pat (pat : pattern) (e: label) =
  (* Does not return its set expression, as it does not require screening *)
  match pat.pat_desc with
  | Tpat_any | Tpat_constant _ -> []
  | Tpat_var (x, _) ->
    init_sc (Id (Id.create !Current.cmtModName x)) [Var (Val e)];
    [(CL.Ident.name x, e)]
  | Tpat_alias (p, x, _) ->
    init_sc (Id (Id.create !Current.cmtModName x)) [Var (Val e)];
    (CL.Ident.name x, e) :: (solve_pat p e)
  | Tpat_tuple pats ->
    pats |> List.mapi (fun idx pat ->
      let temp = Expr.new_temp () in
      init_sc (Var (Val temp)) [Fld (e, (Tuple, Some idx))];
      solve_pat pat temp
    ) |> List.flatten
  | Tpat_construct (_, cstr_desc, pats) ->
    pats |> List.mapi (fun idx pat ->
      let temp = Expr.new_temp () in
      init_sc (Var (Val temp)) [Fld (e, ((Construct cstr_desc), Some idx))];
      solve_pat pat temp
    ) |> List.flatten
  | Tpat_variant (lbl, p_o, _) ->
    let constructor = Variant lbl in
    (match p_o with
    | None -> []
    | Some p ->
      let temp = Expr.new_temp () in
      init_sc (Var (Val temp)) [Fld (e, (constructor, Some 0))];
      solve_pat p temp
    )
  | Tpat_record (fields, _) ->
      fields |> List.map (fun (_, lbl, pat) ->
        let temp = Expr.new_temp () in
        init_sc (Var (Val temp)) [Fld (e, (Record, Some lbl.lbl_pos))];
        solve_pat pat temp) |> List.flatten
  | Tpat_array pats ->
    pats |> List.mapi (fun idx pat ->
      let temp = Expr.new_temp () in
      init_sc (Var (Val temp)) [Fld (e, (Array, Some idx))];
      solve_pat pat temp
    ) |> List.flatten
  | Tpat_lazy p ->
    solve_pat p e
    (* let temp = new_temp_var () in *)
    (* init_sc (Var temp) [App_v (e, [])]; *)
    (* solve_eq p temp update_tbl *)
  | Tpat_or (lhs, rhs, _) ->
    (solve_pat lhs e) @ (solve_pat rhs e)

let se_of_mb (mb : module_binding) =
  let label = label_of_module_expr mb.mb_expr in
  ([Ctor (Member (CL.Ident.name mb.mb_id), [label])], [Var (SideEff label)])

let se_of_vb (vb : value_binding) =
  let bindings = solve_pat vb.vb_pat (label_of_expression vb.vb_expr) in
  let v = bindings |> List.map (fun (name, e) -> Ctor (Member name, [e])) in
  let seff = Var (SideEff (label_of_expression vb.vb_expr)) in
  (v, [seff])

let list_split_flatten l =
  let a, b = List.split l in
  (List.flatten a, List.flatten b)

let se_of_struct_item (item : structure_item) =
  match item.str_desc with
  | Tstr_eval (e, _) -> ([], [Var (SideEff (label_of_expression e))])
  | Tstr_value (_, vbs) ->
    vbs |> List.map se_of_vb |> list_split_flatten
  | Tstr_module mb ->
    se_of_mb mb
  | Tstr_recmodule mbs ->
    mbs |> List.map se_of_mb |> list_split_flatten
  | Tstr_include {incl_mod; incl_type} ->
    let value = label_of_module_expr incl_mod in
    ([Var (Val value)], [])
  | Tstr_primitive vd ->
    let temp = Expr.new_temp () in
    init_sc (Var (Val temp)) [Unknown];
    ([Ctor (Member (CL.Ident.name vd.val_id), [temp])], [])
  | _ -> ([], [])

let se_of_struct str =
  str.str_items |> List.map se_of_struct_item |> list_split_flatten

let se_of_expr expr =
  let solve_param (expr : label) (pattern) : unit =
    solve_pat pattern expr |> ignore
  in
  match expr.exp_desc with
  | Texp_ident (_, _, {val_kind = Val_prim prim}) -> ([Prim prim], [])
  | Texp_ident (x, _, _) -> ([Var (Val (label_of_path x))], [])
  | Texp_constant _ -> ([], [])
  | Texp_let (_, vbs, e) ->
      let _, seff = vbs |> List.map se_of_vb |> list_split_flatten in
    (
      [Var (Val (label_of_expression e))], 
      (Var (SideEff (label_of_expression e))) :: seff
    )
  | Texp_function {cases} ->
    let pats = cases |> List.map (fun case -> case.c_lhs) in
    let bodies = cases |> List.map (fun case -> case.c_rhs) in
    let arg = Expr.new_temp () in
    init_sc (Var (Val arg)) [];
    pats |> List.iter (solve_param arg);
    ([Fn (arg, bodies |> List.map label_of_expression)], [])
  | Texp_apply (e, args) ->
    let arg_labels = args |> List.map (fun (_, aeo) -> Option.map label_of_expression aeo) in
    let seff = args |> List.fold_left (fun acc (_, exp_o) ->
      match exp_o with
      | None -> acc
      | Some exp -> (Var (SideEff (label_of_expression exp))) :: acc
    ) [] in
    let v = [App (label_of_expression e, arg_labels)] in
    let seff = (*  AppSEff (label_of_expression e, arg_labels ) :: *) Var (SideEff (label_of_expression e)) :: seff in
    (v, seff)
  | Texp_match (exp, cases, exn_cases, _) ->
    let pats = cases |> List.map (fun case -> case.c_lhs) in
    let exp_label = label_of_expression exp in
    let () = pats |> List.iter (solve_param exp_label) in
    let rhs_labels = (cases @ exn_cases) |> List.map (fun case -> label_of_expression case.c_rhs) in
    let v = rhs_labels |> List.map (fun label -> Var (Val label)) in
    let seff = rhs_labels |> List.map (fun label -> Var (SideEff label)) in
    (v, Var (SideEff (label_of_expression exp)) :: seff)
  | Texp_try (exp, cases) ->
    let label = label_of_expression exp in
    let ses = cases |> List.map (fun case -> Var (Val (label_of_expression case.c_rhs))) in
    (Var (Val label) :: ses, [Var (SideEff label)])
  | Texp_tuple exps ->
    let v = [Ctor (Tuple, exps |> List.map label_of_expression)] in
    let seff = exps |> List.map (fun e -> Var (SideEff (label_of_expression e))) in
    (v, seff)
  | Texp_construct (_, _, []) ->
    ([], [])
  | Texp_construct (_, cstr_desc, exps) ->
    let v = [Ctor (Construct cstr_desc, exps |> List.map label_of_expression)] in
    let seff = exps |> List.map (fun e -> Var (SideEff (label_of_expression e))) in
    (v, seff)
  | Texp_variant (lbl, Some exp) ->
    let v = [Ctor (Variant lbl, [label_of_expression exp])] in
    let seff = [Var (SideEff (label_of_expression exp))] in
    (v, seff)
  | Texp_variant (_, None) -> ([], [])
  | Texp_record {fields; extended_expression} ->
    let for_each_field ((lbl_desc : label_description), (lbl_def : record_label_definition)) =
      let mem = new_memory !Current.cmtModName in
      init_sc (Mem mem) 
        (match lbl_def with
        | Kept _ ->
          (match extended_expression with
          | Some e -> [Fld (label_of_expression e, (Record, Some lbl_desc.lbl_pos))]
          | None -> [])
        | Overridden (_, e) -> [Var (Val (label_of_expression e))]
        );
      mem
    in
    let v = [Ctor (Record, fields |> Array.map for_each_field |> Array.to_list)] in
    let seff =
      match extended_expression with
      | Some e -> [Var (SideEff (label_of_expression e))]
      | None -> []
    in
    let seff = fields |> Array.fold_left (fun acc (_, lbl_def) ->
      match lbl_def with
      | Kept _ -> acc
      | Overridden (_, e) -> Var (SideEff (label_of_expression e)) :: acc
    ) seff in
    (v, seff)
  | Texp_field (e, _, lbl) ->
    let v = [Fld (label_of_expression e, (Record, Some lbl.lbl_pos))] in
    let seff = [Var (SideEff (label_of_expression e))] in
    (v, seff)
  | Texp_setfield (e1, _, lbl, e2) ->
    let val1 = label_of_expression e1 in
    let val2 = Var (Val (label_of_expression e2)) in
    init_sc (Fld (val1, (Record, Some lbl.lbl_pos))) [val2];
    ([], [SideEffect])
  | Texp_array exps ->
    let for_each_expr_val (expr : expression) =
      let mem = new_memory !Current.cmtModName in
      init_sc (Mem mem) [Var (Val (label_of_expression expr))];
      mem
    in
    let v = [Ctor (Array, exps |> List.map for_each_expr_val)] in
    let seff = exps |> List.map (fun e -> Var (SideEff (label_of_expression e))) in
    (v, seff)
  | Texp_ifthenelse (exp, exp_true, Some exp_false) ->
    let val1 = Var (Val (label_of_expression exp_true)) in
    let val2 = Var (Val (label_of_expression exp_false)) in
    let seff0 = Var (SideEff (label_of_expression exp)) in
    let seff1 = Var (SideEff (label_of_expression exp_true)) in
    let seff2 = Var (SideEff (label_of_expression exp_false)) in
    ([val1; val2], [seff0; seff1; seff2])
  | Texp_ifthenelse (exp, exp_true, None) ->
    let seff0 = Var (SideEff (label_of_expression exp)) in
    let seff1 = Var (SideEff (label_of_expression exp_true)) in
    ([Var (Val (label_of_expression exp_true))], [seff0; seff1])
  | Texp_while (exp_cond, exp_body) ->
    let seff_cond = Var (SideEff (label_of_expression exp_cond)) in
    let seff_body = Var (SideEff (label_of_expression exp_body)) in
    ([], [seff_cond; seff_body])
  | Texp_for (x, _, exp1, exp2, _, exp_body) ->
    init_sc (Id (Id.create !Current.cmtModName x)) [];
    let seff1 = Var (SideEff (label_of_expression exp1)) in
    let seff2 = Var (SideEff (label_of_expression exp2)) in
    let seff_body = Var (SideEff (label_of_expression exp_body)) in
    ([], [seff1; seff2; seff_body])
  | Texp_letmodule (x, _, me, e) ->
    let val_m = Var (Val (label_of_module_expr me)) in
    let val_e = Var (Val (label_of_expression e)) in
    init_sc (Id (Id.create !Current.cmtModName x)) [val_m];
    let seff_m = Var (SideEff (label_of_module_expr me)) in
    let seff_e = Var (SideEff (label_of_expression e)) in
    ([val_e], [seff_m; seff_e])
  | Texp_pack me ->
      ([Var (Val (label_of_module_expr me))], [Var (SideEff (label_of_module_expr me))])
  | _ -> ([], [])

let se_of_module_expr (m : CL.Typedtree.module_expr) =
  match m.mod_desc with
  | Tmod_functor (x, _, _, me) ->
      let temp = Expr.new_temp () in
      init_sc (Var (Val temp)) [Id (Id.create !Current.cmtModName x)];
    ([Fn (temp, [label_of_module_expr me])], [])
  | Tmod_ident (x, _) ->
    let x = label_of_path x in
    ([Var (Val x)], [])
  | Tmod_structure structure -> se_of_struct structure
  | Tmod_apply (func, arg, _) ->
    let v = [App (label_of_module_expr func, [Some (label_of_module_expr arg)])] in
    let seff_f = Var (SideEff (label_of_module_expr func)) in
    let seff_arg = Var (SideEff (label_of_module_expr arg)) in
    (v, [seff_f; seff_arg])
  | Tmod_constraint (m, _, _, _) ->
    ([Var (Val (label_of_module_expr m))], [Var (SideEff (label_of_module_expr m))])
  | Tmod_unpack (e, _) ->
    ([Var (Val (label_of_expression e))], [Var (SideEff (label_of_expression e))])

let traverse_ast =
  let super = CL.Tast_mapper.default in
  let expr self (expr : expression) =
    let v, seff = se_of_expr expr in
    (* ValueAnalysis.addExpression e se; *)
    init_sc (Var (Val (label_of_expression expr))) v;
    init_sc (Var (SideEff (label_of_expression expr))) seff;
    super.expr self expr
  in
  let module_expr self (me : module_expr) =
    let v, seff = se_of_module_expr me in
    init_sc (Var (Val (label_of_module_expr me))) v;
    init_sc (Var (SideEff (label_of_module_expr me))) seff;
    (* ValueAnalysis.addModuleExpression me se; *)
    super.module_expr self me
  in
  {super with expr; module_expr}

let preprocess =
  let super = CL.Tast_mapper.default in
  let expr self e =
    let e' = Expr.preprocess_expression e in
    super.expr self e'
  in
  let module_expr self me =
    let me' = Expr.preprocess_module_expr me in
    super.module_expr self me'
  in
  {super with expr; module_expr}

let processCmtStructure modname (structure : CL.Typedtree.structure) =
  (* print_endline "processCmtStructure"; *)
  (* print_endline modname; *)
  (* Print.print_structure structure; *)
  (* print_newline (); *)
  let structure = structure |> preprocess.structure preprocess in
  structure |> traverse_ast.structure traverse_ast |> ignore;
  (* FIXME: use cmt module's side effect *)
  let v, seff = se_of_struct structure in
  init_sc (Id (Id.createCmtModuleId modname)) v;
  ()

let processCmt (cmt_infos : CL.Cmt_format.cmt_infos) =
  Current.cmtModName := cmt_infos.cmt_modname;
  (* let moduleId = Id.createCmtModuleId !Current.cmtModName in *)
  match cmt_infos.cmt_annots with
  | Interface _ -> ()
  | Implementation structure ->
    processCmtStructure cmt_infos.cmt_modname structure
  | _ -> ()


let get_context label = fst label


module PrimResolution = struct
  let allocated = Hashtbl.create 10

  let value_prim : (CL.Primitive.description * label list) -> SESet.t * SESet.t = function
    | {prim_name = "%revapply"}, [x; y] ->
      (SESet.singleton (App (y, [Some x])), SESet.empty)
    | {prim_name = "%apply"}, [x; y] ->
      (SESet.singleton (App (x, [Some y])), SESet.empty)
    | {prim_name = "%identity" | "%opaque"}, [x] ->
      (SESet.singleton (Var (Val x)), SESet.empty)
    | {prim_name = "%ignore"}, [_] -> (SESet.empty, SESet.empty)
    | {prim_name = "%field0"}, [x] ->
      (SESet.singleton (Fld (x, (Tuple, Some 0))), SESet.empty)
    | {prim_name = "%field1"}, [x] ->
      (SESet.singleton (Fld (x, (Tuple, Some 1))), SESet.empty)
    | {prim_name = "%setfield0"}, [x; y] ->
      update_sc (Fld (x, (Record, Some 0))) (SESet.singleton (Var (Val y )));
      (SESet.empty, SESet.singleton SideEffect)
    | {prim_name = "%makemutable"}, [x] -> (
      let value = SESet.singleton (Var (Val x)) in
      match Hashtbl.find allocated x with
      | exception Not_found ->
        let i = new_memory (get_context x) in
        Hashtbl.add allocated x i;
        update_sc (Mem i) value;
        (SESet.singleton (Ctor (Record, [i])), SESet.empty)
      | i ->
        update_sc (Mem i) value;
        (SESet.singleton (Ctor (Record, [i])), SESet.empty)
    )
    | {prim_name = "%lazy_force"}, [x] -> (SESet.singleton (App (x, [])), SESet.empty)
    | ( {
          prim_name =
            ( "%eq" | "%noteq" | "%ltint" | "%leint" | "%gtint" | "%geint"
            | "%eqfloat" | "%noteqfloat" | "%ltfloat" | "%lefloat" | "%gtfloat"
            | "%gefloat" | "%equal" | "%notequal" | "%lessequal" | "%lessthan"
            | "%greaterequal" | "%greaterthan" | "%compare" | "%boolnot"
            | "%sequand" | "%sequor" );
        },
        _ ) ->
      (SESet.empty, SESet.empty)
    | ( {
          prim_name =
            "%raise" | "%reraise" | "%raise_notrace" | "%raise_with_backtrace";
        },
        _ ) ->
      (SESet.empty, SESet.empty)
    | _ -> (SESet.singleton Unknown, SESet.singleton SideEffect)

end

let rec front_arg_len = function
  | [] -> 0
  | None :: _ -> 0
  | Some _ :: tl -> front_arg_len tl + 1

let rec split_arg n args =
  match n with
  | 0 -> ([], args)
  | _ ->
      match args with
      | Some hd :: tl ->
          let hds, rem = split_arg (n-1) tl in
          (hd :: hds, rem)
      | _ -> raise (RuntimeError "Invalid args")

let rec merge_args = function
  | [], l -> l
  | l, [] -> l
  | None :: tl, hd :: l -> hd :: merge_args (tl, l)
  | Some x :: tl, l -> Some x :: merge_args (tl, l)

let rec reduce_app f args =
  match args with
  | [] | None :: _ -> (SESet.empty, SESet.empty)
  | Some hd :: tl ->
    match f with
    | Unknown ->
      args |> List.iter (fun arg ->
        match arg with
        | None -> ()
        | Some label -> update_sc AppliedToUnknown (SESet.singleton (Var (Val label)));
      );
      (SESet.singleton Unknown, SESet.singleton SideEffect)
    | Fn (param, bodies) ->
      let value =
        bodies
          |> List.map (fun body -> if tl = [] then Var (Val body) else App (body, tl))
          |> SESet.of_list
      in
      let seff =
        bodies
          |> List.map (fun body -> Var (SideEff body))
          |> SESet.of_list
      in
      update_sc (Var (Val param)) (SESet.singleton (Var (Val hd)));
      (value, seff)
    | Prim p ->
      if front_arg_len args >= p.prim_arity then (
        let prim_args, tl = split_arg p.prim_arity args in
        let value, seff = PrimResolution.value_prim (p, prim_args) in
        match tl with
        | [] -> (value, seff)
        | _ ->
            SESet.fold (fun se (acc_value, acc_seff) ->
              let value', seff' = reduce_app se tl in
              (SESet.union acc_value value', SESet.union acc_seff seff')
            ) value (SESet.empty, seff)
      ) else (SESet.singleton (PrimApp (p, args)), SESet.empty)
    | App (e, None :: tl') ->
      (SESet.singleton (App (e, Some hd :: merge_args (tl', tl))), SESet.empty)
    | PrimApp (p, args') when front_arg_len args' < p.prim_arity ->
      let args = merge_args (args', args) in
      if front_arg_len args >= p.prim_arity then (
        let prim_args, tl = split_arg p.prim_arity args in
        let value, seff = PrimResolution.value_prim (p, prim_args) in
        match tl with
        | [] -> value, seff
        | _ ->
          SESet.fold (fun se (acc_value, acc_seff) ->
            let value', seff' = reduce_app se tl in
            (SESet.union acc_value value', SESet.union acc_seff seff')
          ) value (SESet.empty, seff)
      ) else (SESet.singleton (PrimApp (p, args)), SESet.empty)
    | _ -> (SESet.empty, SESet.empty)

let propagate = function
  | Unknown | Ctor _ | Prim _ | Fn _
  | App (_, None :: _)
  | PrimApp _ ->
    true
  | SideEffect -> true
  | _ -> false

let reduce_fld se fld =
  match se with
  | Unknown -> SESet.singleton Unknown
  | Ctor (kappa, l) -> (
    match fld with
    | kappa', Some i -> (
      try
        if kappa = kappa' then
          let ith = Mem (List.nth l i) in
          SESet.singleton ith
        else SESet.empty
      with _ -> SESet.empty)
    | _ -> SESet.empty)
  | _ -> SESet.empty

let reduce_value se =
  match se with
  | Unknown | Ctor _ | Fn _ | Mem _
  | App (_, None :: _)
  | PrimApp _
  | Prim _ ->
    (SESet.empty, SESet.empty)
  | App (e, (Some _ :: _ as arg)) ->
    SESet.fold
      (fun se (acc_value, acc_seff) ->
        let value, seff = reduce_app se arg in
        (SESet.union value acc_value, SESet.union seff acc_seff))
      (lookup_sc (Var (Val e))) (SESet.empty, SESet.empty)
  | Fld (e, fld) ->
    let value = 
    SESet.fold
      (fun se acc ->
        let to_add = reduce_fld se fld in
        SESet.union to_add acc)
      (lookup_sc (Var (Val e))) SESet.empty
      in (value, SESet.empty)
  | Var (Val e) ->
    let set = SESet.filter propagate (lookup_sc (Var (Val e))) in
    (set, SESet.empty)
  | Id x ->
    let set = SESet.filter propagate (lookup_sc (Id x)) in
    (set, SESet.empty)
  | _ -> failwith "Invalid value se"

let reduce_seff se =
  match se with
  | SideEffect -> SESet.empty
  | Var (SideEff e) ->
    let set = SESet.filter propagate (lookup_sc (Var (SideEff e))) in
    set
  | _ ->
      PrintSE.print_se se;
      failwith "Invalid side effect se"

let reduce_structured_value se =
  match se with
  | Var (Val e) ->
    SESet.filter propagate (lookup_sc (Var (Val e)))
  | Fn (arg, _) ->
    update_sc (Var (Val arg)) (SESet.singleton Unknown);
    SESet.empty
  | Ctor (Record, mems) ->
      mems |> List.fold_left (fun acc mem ->
        let field_values = SESet.filter propagate (lookup_sc (Mem mem)) in
        SESet.union acc field_values) SESet.empty
  | Ctor (_, labels) ->
      labels |> List.fold_left (fun acc label ->
        let field_values = SESet.filter propagate (lookup_sc (Var (Val label))) in
        SESet.union acc field_values) SESet.empty
  | Unknown | Prim _ -> SESet.empty
  | App (e, None :: _) -> SESet.singleton (Var (Val e))
  | _ ->
      PrintSE.print_se se;
      failwith "Invalid structured value"

let step_sc_for_entry x =
  let set = lookup_sc x in
  match x with
  | Mem _ | Id _ ->
    let reduced =
      SESet.fold
        (fun se acc ->
          let value, _ = reduce_value se in
          SESet.union value acc)
        set SESet.empty
    in
    update_sc x reduced
  | Var (Val e) ->
    let value, seff =
      SESet.fold
        (fun se (acc_value, acc_seff) ->
          let value, seff = reduce_value se in
          (SESet.union value acc_value, SESet.union seff acc_seff))
        set (SESet.empty, SESet.empty)
    in
    update_sc (Var (Val e)) value;
    update_sc (Var (SideEff e)) seff
  | Var (SideEff _) ->
    let reduced =
      SESet.fold
        (fun se acc ->
          let seff = reduce_seff se in
          SESet.union seff acc)
        set SESet.empty
    in
    update_sc x reduced
  | Fld (e, (Record, Some i)) ->
    (lookup_sc (Var (Val e))) |> SESet.iter (function
      | Ctor (Record, l) -> (
        try update_sc (Mem (List.nth l i)) set with _ -> ())
      | _ -> ())
  | AppliedToUnknown ->
    let reduced =
      SESet.fold
        (fun se acc ->
          let value = reduce_structured_value se in
          SESet.union value acc)
        set SESet.empty
    in
    update_sc x reduced
  | _ -> failwith "Invalid LHS"

let step_sc () =
  let to_be_reduced =
    SESet.fold
      (fun idx acc ->
        SESet.union
          (try Hashtbl.find reverse_sc idx with Not_found -> SESet.empty)
          acc)
      !prev_worklist SESet.empty
  in
  to_be_reduced |> SESet.iter step_sc_for_entry

let solve () =
  Format.flush_str_formatter () |> ignore;
  changed := true;
  while !changed do
    print_endline "step";
    changed := false;
    Worklist.prepare_step worklist prev_worklist;
    step_sc ()
  done

let reportDead ~ppf =
  solve ();
  (* PrintSE.print_sc_info (); *)
  ()
