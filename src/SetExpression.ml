open CL.Types
open CL.Typedtree

module Current = struct
  let cmtModName : string ref = ref ""
end

module Id = struct
  (* Ident.t is unique under a module file, except for the ident of top-level module (persistent). *)
  (* Then Ident.t with top-level module name is unique for whole codebase. *)
  type t = string * CL.Ident.t

  let createCmtModuleId modname : t =
    ("+", {name = modname; stamp = 0; flags = 0})

  let create ctx ident : t =
    match CL.Ident.persistent ident with
    | true -> createCmtModuleId (CL.Ident.name ident)
    | false -> (ctx, ident)

  let ident (id : t) = snd id
  let ctx (id : t) = fst id
  let name id = id |> ident |> CL.Ident.name
  let hash id = CL.Ident.hash (snd id)

  let compare a b =
    let c = String.compare (ctx a) (ctx b) in
    if c <> 0 then c else CL.Ident.compare (ident a) (ident b)

  let equal a b =
    String.equal (ctx a) (ctx b) && CL.Ident.equal (ident a) (ident b)

  let to_string (id : t) =
    Printf.sprintf "[%s]%s#%d" (ctx id) (name id) (ident id).stamp

  let print (id : t) =
    Printf.printf "[%s]%s#%d" (ctx id) (name id) (ident id).stamp
end

module IdTbl = Hashtbl.Make (Id)
module IdSet = Set.Make (Id)

module Label = struct
  type t = string * int

  type value_expr_summary = {
    exp : expression;
    exp_type : CL.Types.type_expr;
    exp_loc : CL.Location.t;
    exp_context : string;
  }

  type module_expr_summary = {
    mod_exp : module_expr;
    mod_type : CL.Types.module_type;
    mod_loc : CL.Location.t;
    mod_context : string;
  }

  type summary =
    | ValueExpr of value_expr_summary
    | ModExpr of module_expr_summary
    | CmtModule of string
    | FnParam of CL.Ident.t
    | Path of CL.Path.t
    | Tmp

  let to_summary_tbl : (t, summary) Hashtbl.t = Hashtbl.create 10
  let to_summary label = Hashtbl.find to_summary_tbl label
  let label_tbl = Hashtbl.create 10

  let new_label mod_name : t =
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
    let mod_name, num = label in
    let loc : Lexing.position =
      {pos_fname = mod_name; pos_lnum = num; pos_bol = 0; pos_cnum = -1}
    in
    {loc_start = loc; loc_end = loc; loc_ghost = true}

  let preprocess_expression (e : expression) =
    let label = new_label !Current.cmtModName in
    Hashtbl.add to_summary_tbl label
      (ValueExpr
         {
           exp = e;
           exp_type = e.exp_type;
           exp_loc = e.exp_loc;
           exp_context = !Current.cmtModName;
         });
    {e with exp_loc = new_loc label}

  let of_expression (e : expression) =
    let pos = e.exp_loc.loc_start in
    (pos.pos_fname, pos.pos_lnum)

  let preprocess_module_expr (me : module_expr) =
    let label = new_label !Current.cmtModName in
    Hashtbl.add to_summary_tbl label
      (ModExpr
         {
           mod_exp = me;
           mod_type = me.mod_type;
           mod_loc = me.mod_loc;
           mod_context = !Current.cmtModName;
         });
    {me with mod_loc = new_loc label}

  let of_module_expr (me : module_expr) =
    let pos = me.mod_loc.loc_start in
    (pos.pos_fname, pos.pos_lnum)

  let new_temp () =
    let label = new_label !Current.cmtModName in
    Hashtbl.add to_summary_tbl label Tmp;
    label

  let new_param id =
    let label = new_label !Current.cmtModName in
    Hashtbl.add to_summary_tbl label (FnParam id);
    label

  let new_path path =
    let label = new_label !Current.cmtModName in
    Hashtbl.add to_summary_tbl label (Path path);
    label

  let new_cmt_module modname =
    let label = new_label modname in
    Hashtbl.add to_summary_tbl label (CmtModule modname);
    label
end

type var = Val of Label.t | SideEff of Label.t
type arg = Label.t option list
type memory_label = string * int

type ctor =
  | Variant of string
  | Construct of string
  | Record
  | Tuple
  | Member of string
  | Array

module CtorMap = Map.Make (struct
  type t = ctor

  let compare = compare
end)

type fld = ctor * int option
type case = {pat : pattern; guard : var option; expr : var}

type se =
  | Top
  (* Set variable *)
  | Var of var
  | Id of Id.t
  (* Value *)
  | Unknown
  | Mem of memory_label
  | Prim of CL.Primitive.description
  | Fn of Label.t * Label.t list
  | App of Label.t * arg
  | PrimApp of CL.Primitive.description * arg
  | Ctor of ctor * Label.t list
  | Fld of Label.t * fld
  (* Side Effect *)
  | SideEffect
  | AppliedToUnknown

let compare_se a b =
  match (a, b) with Id x, Id y -> Id.compare x y | _ -> compare a b

module SESet = Set.Make (struct
  type t = se

  let compare = compare_se
end)

let compare_se_pair (a1, a2) (b1, b2) =
  match compare_se a1 b1 with 0 -> compare_se a2 b2 | c -> c

module SEPairSet = Set.Make (struct
  type t = se * se

  let compare = compare_se_pair
end)

module SETbl = Hashtbl.Make (struct
  type t = se

  let compare = compare_se
  let equal a b = match (a, b) with Id x, Id y -> Id.equal x y | _ -> a = b
  let hash = function Id x -> Id.hash x | x -> Hashtbl.hash x
end)

type workitem = WorkPair of se * se | WorkKey of se

module WorkItemSet = Set.Make (struct
  type t = workitem

  let compare a b =
    match (a, b) with
    | WorkKey x, WorkKey y -> compare_se x y
    | WorkPair (x1, x2), WorkPair (y1, y2) -> compare_se_pair (x1, x2) (y1, y2)
    | _ -> compare a b
end)

module Worklist = struct
  type t = WorkItemSet.t ref

  let add x (worklist : t) = worklist := WorkItemSet.add x !worklist
  let addset s (worklist : t) = worklist := WorkItemSet.union s !worklist
  (* let mem x (worklist : t) = SESet.mem x !worklist *)

  let prepare_step (worklist : t) (prev_worklist : t) =
    prev_worklist := !worklist;
    worklist := WorkItemSet.empty

  let create () = ref WorkItemSet.empty
  let clear worklist = worklist := WorkItemSet.empty
end

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

let updated : (se * se) list ref = ref []
let worklist : Worklist.t = Worklist.create ()

(* let prev_worklist : Worklist.t = ref SEPairSet.empty *)
let sc : SESet.t SETbl.t = SETbl.create 256
let reverse_sc : WorkItemSet.t SETbl.t = SETbl.create 256
let changed = ref false

let lookup_sc se =
  try SETbl.find sc se with Not_found -> SESet.singleton Unknown

(* exception Escape *)
(* let update_worklist key set = *)
(*   let summarize elt = *)
(*     let idx = *)
(*       match elt with *)
(*       | App (e, (Some _ :: _ | [])) *)
(*       | Fld (e, _) -> *)
(*         Worklist.add (Var (Val e)) worklist; *)
(*         Var (Val e) *)
(*       | Var _ | Mem _ | Id _ -> *)
(*         Worklist.add elt worklist; *)
(*         elt *)
(*       | _ -> Worklist.add elt worklist; elt *)
(*       (1* | _ -> raise Escape *1) *)
(*     in *)
(*     match SETbl.find_opt reverse_sc idx with *)
(*     | None -> SETbl.add reverse_sc idx (SESet.singleton key) *)
(*     | Some orig -> SETbl.replace reverse_sc idx (SESet.add key orig) *)
(*   in *)
(*   match key with *)
(*   | Mem _ | Id _ -> *)
(*     Worklist.add key worklist; *)
(*     SESet.iter (fun se -> try summarize se with Escape -> ()) set *)
(*   | Var _ -> *)
(*     Worklist.add key worklist; *)
(*     SESet.iter (fun se -> try summarize se with Escape -> ()) set *)
(*   | Fld (e, _) -> summarize (Var (Val e)) *)
(*   | AppliedToUnknown -> *)
(*     Worklist.add key worklist; *)
(*     SESet.iter (fun se -> try summarize se with Escape -> ()) set *)
(*   | _ -> failwith "Invalid LHS" *)

let rec front_arg_len = function
  | [] -> 0
  | None :: _ -> 0
  | Some _ :: tl -> front_arg_len tl + 1

let propagate = function
  | Unknown | Ctor _ | Prim _ | Fn _ | App (_, None :: _) -> true
  | PrimApp (prim, args) -> front_arg_len args < prim.prim_arity
  | SideEffect -> true
  | _ -> false

let add_reverse se workitem =
  match SETbl.find_opt reverse_sc se with
  | None -> SETbl.add reverse_sc se (WorkItemSet.singleton workitem)
  | Some orig -> SETbl.replace reverse_sc se (WorkItemSet.add workitem orig)

let update_worklist (key, elt) =
  Worklist.add (WorkPair (key, elt)) worklist;
  match key with
  | Mem _ | Id _ | Var _ -> (
    add_reverse elt (WorkPair (key, elt));
    (if propagate elt then
     match SETbl.find_opt reverse_sc key with
     | Some rev -> Worklist.addset rev worklist
     | None -> ());
    match (key, elt) with
    | Var _, Fld (e, _) | Var _, App (e, Some _ :: _) ->
      add_reverse (Var (Val e)) (WorkPair (key, elt))
    | _ -> ())
  | Fld (e, _) -> add_reverse (Var (Val e)) (WorkPair (key, elt))
  | AppliedToUnknown -> add_reverse elt (WorkPair (key, elt))
  | _ -> failwith "Invalid LHS"

(* enforce data to be nonempty *)
let init_sc lhs data =
  data |> List.iter (fun rhs -> updated := (lhs, rhs) :: !updated);
  let set = SESet.of_list data in
  (* update_worklist lhs set; *)
  match SETbl.find sc lhs with
  | exception Not_found -> SETbl.add sc lhs set
  | original -> SETbl.replace sc lhs (SESet.union original set)

let update_sc lhs added =
  let original = lookup_sc lhs in
  let diff = SESet.diff added original in
  if not (SESet.is_empty diff) then (
    changed := true;
    diff |> SESet.iter (fun rhs -> updated := (lhs, rhs) :: !updated);
    (* diff |> SESet.iter (update_worklist lhs); *)
    (* update_worklist lhs diff; *)
    SETbl.replace sc lhs (SESet.union original diff))
