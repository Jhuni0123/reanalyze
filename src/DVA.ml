open CL.Typedtree
open CL.Types

exception RuntimeError of string

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

(* Expression ID mapping *)
module Expr = struct
  type id = string

  let counter = ref 0

  let new_loc () =
    counter := !counter + 1;
    CL.Location.in_file ("_expr_" ^ string_of_int !counter)

  let toId e = e.exp_loc.loc_start.pos_fname
  let fromIdTbl : (id, expression) Hashtbl.t = Hashtbl.create 256
  let origLocTbl : (id, CL.Location.t) Hashtbl.t = Hashtbl.create 256
  let fromId eid = Hashtbl.find fromIdTbl eid
  let origLoc e = Hashtbl.find origLocTbl (toId e)

  let preprocess e =
    let origLoc = e.exp_loc in
    let e = {e with exp_loc = new_loc ()} in
    Hashtbl.add fromIdTbl (toId e) e;
    Hashtbl.add origLocTbl (toId e) origLoc;
    e
end

(* Function ID mapping *)
type fnbody = {cmtModName : string; pat : pattern; exp_id : Expr.id}

let idToBody : (Expr.id, fnbody list) Hashtbl.t = Hashtbl.create 256
let bodyOfFunction eid = Hashtbl.find idToBody eid

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

module Value = struct
  type t = V_Expr of Expr.id | V_Mutable of Expr.id * string | V_Name of Id.t

  let expr e = V_Expr (Expr.toId e)
  let mutableField e f = V_Mutable (Expr.toId e, f)

  let compare a b =
    match (a, b) with
    | V_Name id1, V_Name id2 -> Id.compare id1 id2
    | _ -> compare a b

  let print v =
    match v with
    | V_Expr eid ->
      Printf.printf "Expr(%s,%s)" eid
        (eid |> Expr.fromId |> Expr.origLoc |> string_of_loc)
    | V_Mutable (et, s) -> Printf.printf "Mut(%s)" s
    | V_Name id ->
      print_string "Name(";
      Id.print id;
      Printf.printf ")"
end

module ValueSet = Set.Make (Value)

module Field = struct
  type t = F_Record of string | F_Tuple of int

  let compare = compare
end

module ValueExpression = struct
  type t =
    | VE_Expr of Expr.id
    | VE_Mutable of Expr.id * string
    | VE_Name of Id.t (* except primitive *)
    | VE_Prim of CL.Primitive.description
    | VE_Cstr of constructor_description * Expr.id list
    | VE_Variant of string * Expr.id
    | VE_Field of Field.t * Expr.id
    | VE_Fn of Expr.id * CL.Ident.t (* (λx.e)_l *)
    | VE_PartialApp of
        Expr.id * Expr.id option list (* first arg is none: e [_ e1 e2] *)
    | VE_FnSideEffect

  let compare a b =
    match (a, b) with
    | VE_Name id1, VE_Name id2 -> Id.compare id1 id2
    | _ -> compare a b

  let expr e = VE_Expr (Expr.toId e)

  let print v =
    match v with
    | VE_Expr eid -> Printf.printf "Expr(%s)" eid
    | VE_Mutable (et, s) -> Printf.printf "Mut(%s)" s
    | VE_Name id -> Printf.printf "Name(%s)" (Id.name id)
    | VE_Prim prim -> Printf.printf "Prim(%s)" prim.prim_name
    | VE_Cstr (cstr_desc, eids) ->
      Printf.printf "Cstr-%s(" cstr_desc.cstr_name;
      Print.print_list (fun eid -> print_string eid) "," eids;
      print_string ")"
    | VE_Variant (k, eid) -> Printf.printf "Variant(%s,%s)" k eid
    | VE_Field (f, eid) ->
      Printf.printf "Field(%s,%s)"
        (match f with F_Record f -> f | F_Tuple n -> string_of_int n)
        eid
    | VE_Fn (eid, param) -> Printf.printf "Fn(%s)" param.name
    | VE_PartialApp (eid, args) ->
      Printf.printf "App(%s,[" eid;
      None :: args
      |> Print.print_list
           (fun argo ->
             match argo with
             | None -> print_string "-"
             | Some eid -> print_string eid)
           ",";
      print_string "])"
    | VE_FnSideEffect -> Printf.printf "λ.φ"
end

module Reduction = struct
  type t = Reduce of Expr.id * Expr.id * Expr.id option list (* e [e1, ...] *)

  let compare = compare
end

open Value
module VE = ValueExpression
open Reduction
module ReductionSet = Set.Make (Reduction)
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

module VESet = struct
  module ElemSet = Set.Make (ValueExpression)

  type t = VS_Top | VS_Set of ElemSet.t

  let singleton v = VS_Set (ElemSet.singleton v)
  let empty = VS_Set ElemSet.empty
  let compare = compare

  let join a b =
    match (a, b) with
    | VS_Top, _ | _, VS_Top -> VS_Top
    | VS_Set s1, VS_Set s2 -> VS_Set (ElemSet.union s1 s2)

  let add vs v =
    match vs with
    | VS_Top -> VS_Top
    | VS_Set s ->
      let s' = ElemSet.add v s in
      if s == s' then vs else VS_Set s'

  let subset s1 s2 =
    match (s1, s2) with
    | _, VS_Top -> true
    | VS_Top, _ -> false
    | VS_Set s1', VS_Set s2' -> ElemSet.subset s1' s2'

  let print vs =
    match vs with
    | VS_Top -> print_string "Top"
    | VS_Set s ->
      s |> ElemSet.elements |> Print.print_list ValueExpression.print ", "

  let mem k vs = match vs with VS_Top -> true | VS_Set s -> s |> ElemSet.mem k
end

module VClosure = struct
  type t = {
    mutable passedToUnknown : bool;
    mutable values : VESet.t;
    (* for expression only *)
    mutable reductions : ReductionSet.t;
    mutable sideEffect : bool;
  }

  let init () =
    {
      passedToUnknown = false;
      reductions = ReductionSet.empty;
      sideEffect = false;
      values = VESet.empty;
    }

  let addValue v vc =
    match vc.values |> VESet.mem v with
    | true -> false
    | false ->
      vc.values <- VESet.add vc.values v;
      true

  let addVESet vs vc =
    match VESet.subset vs vc.values with
    | true -> false
    | false ->
      vc.values <- VESet.join vs vc.values;
      true

  let markSideEffect vc =
    match vc.sideEffect with
    | true -> false
    | false ->
      vc.sideEffect <- true;
      true

  let addReduction reduce vc =
    match vc.reductions |> ReductionSet.mem reduce with
    | true -> false
    | false ->
      vc.reductions <- vc.reductions |> ReductionSet.add reduce;
      true

  let markPassedToUnknown vc =
    match vc.passedToUnknown with
    | true -> false
    | false ->
      vc.passedToUnknown <- true;
      true
end

module ValueDependency = struct
  type func = Live.t -> Live.t

  type t = {
    mutable adj : (Value.t * func) list;
    mutable rev_adj : (Value.t * func) list;
  }

  let createEmpty () = {adj = []; rev_adj = []}
end

module ValueAnalysis = struct
  type t = {
    value : Value.t;
    loc : CL.Location.t;
    value_type : type_expr;
    closure : VClosure.t;
    mutable liveness : Live.t;
    dependency : ValueDependency.t;
  }

  let shouldReport (va : t) =
    (not va.loc.loc_ghost)
    && Suppress.filter va.loc.loc_start
    &&
    match va.value with
    | V_Expr eid ->
      let e = Expr.fromId eid in
      (not (isUnitType e.exp_type)) && not (isEmptyPropsType e.exp_type)
    | _ -> true

  let report ppf va =
    let loc = va.loc in
    let name =
      match va.value with
      | V_Expr eid -> ""
      | V_Mutable _ -> "<memory>"
      | V_Name id -> Printf.sprintf "[%s]%s" (Id.ctx id) (Id.name id)
    in
    if shouldReport va then
      Log_.warning ~loc ~name:"Warning Dead Value" (fun ppf () ->
          match va.value with
          | V_Expr eid ->
            let e = Expr.fromId eid in
            Format.fprintf ppf "\n";
            Print.print_expression 0 e;
            print_newline ();
            Print.print_type e.exp_type
          | V_Mutable _ -> Format.fprintf ppf "<mutable field>"
          | V_Name id -> Format.fprintf ppf "%s" name)

  let tbl : (Value.t, t) Hashtbl.t = Hashtbl.create 10

  let get : Value.t -> t = function
    | vm -> (
      match Hashtbl.find_opt tbl vm with
      | Some va -> va
      | None ->
        Value.print vm;
        print_newline ();
        raise (RuntimeError "Value not found"))

  let joinLive v live =
    let va = get v in
    va.liveness <- Live.join va.liveness live

  let isSideEffectFn v =
    let va = get v in
    va.closure.values |> VESet.mem VE_FnSideEffect

  let hasSideEffect e =
    let va = get (Value.expr e) in
    va.closure.sideEffect

  let addValue v l t =
    Hashtbl.add tbl v
      {
        value = v;
        loc = l;
        value_type = t;
        closure = VClosure.init ();
        liveness = Live.Bot;
        dependency = ValueDependency.createEmpty ();
      }

  let addExpr eid (e : expression) = addValue (V_Expr eid) e.exp_loc e.exp_type
  let addId (id : Id.t) loc te = addValue (V_Name id) loc te

  let addMutableField eid e label_desc =
    addValue (V_Mutable (eid, label_desc.lbl_name)) e.exp_loc label_desc.lbl_arg

  let addDependency v1 v2 f =
    let d1 = (get v1).dependency in
    let d2 = (get v2).dependency in
    d1.adj <- (v2, f) :: d1.adj;
    d2.rev_adj <- (v1, f) :: d2.rev_adj

  let scc () : Value.t list list =
    let counter = ref 0 in
    let stack = Stack.create () in
    let num = Hashtbl.create 256 in
    let getnum vm =
      match Hashtbl.find_opt num vm with Some res -> res | None -> 0
    in
    let finished = ref ValueSet.empty in
    let markfinished vm = finished := !finished |> ValueSet.add vm in
    let isfinished vm = !finished |> ValueSet.mem vm in
    let scc = Stack.create () in
    let rec dfs v =
      counter := !counter + 1;
      Hashtbl.add num v !counter;
      stack |> Stack.push v;
      let result =
        (get v).dependency.adj
        |> List.fold_left
             (fun result (next, _) ->
               if getnum next = 0 then min result (dfs next)
               else if not (isfinished next) then min result (getnum next)
               else result)
             (getnum v)
      in
      if result = getnum v then (
        let nodes = Stack.create () in
        let break = ref false in
        while not !break do
          let t = stack |> Stack.pop in
          nodes |> Stack.push t;
          markfinished t;
          if Value.compare t v = 0 then break := true
        done;
        scc |> Stack.push (nodes |> Stack.to_seq |> List.of_seq));
      result
    in
    tbl |> Hashtbl.to_seq_keys
    |> Seq.iter (fun node -> if getnum node = 0 then dfs node |> ignore);
    scc |> Stack.to_seq |> List.of_seq
end

module ModuleEnv = struct
  let env : (string, IdSet.t) Hashtbl.t IdTbl.t = IdTbl.create 10

  let addMember (parent : Id.t) (child : Id.t) =
    match IdTbl.find_opt env parent with
    | Some tbl ->
      let set =
        match Hashtbl.find_opt tbl (Id.name child) with
        | Some set -> set |> IdSet.add child
        | None -> IdSet.singleton child
      in
      Hashtbl.replace tbl (Id.name child) set
    | None ->
      let tbl = Hashtbl.create 10 in
      Hashtbl.add tbl (Id.name child) (IdSet.singleton child);
      IdTbl.add env parent tbl

  let resolvePath currentMod (path : CL.Path.t) : IdSet.t =
    let rec _findIdents (p : CL.Path.t) : IdSet.t =
      match p with
      | Pident id -> (
        match CL.Ident.persistent id with
        | true -> IdSet.singleton (Id.createCmtModuleId (CL.Ident.name id))
        | false -> IdSet.singleton (Id.create currentMod id))
      | Pdot (sub, name, _) ->
        let parents = _findIdents sub in
        IdSet.fold
          (fun parent acc ->
            match IdTbl.find_opt env parent with
            | Some tbl -> (
              match Hashtbl.find_opt tbl name with
              | None -> acc
              | Some set -> IdSet.union set acc)
            | None -> acc)
          parents IdSet.empty
      | Papply _ -> IdSet.empty
    in
    _findIdents path

  let print () =
    env
    |> IdTbl.iter (fun id tbl ->
           Id.print id;
           print_endline ":";
           tbl
           |> Hashtbl.iter (fun name idset ->
                  idset
                  |> IdSet.iter (fun id' ->
                         print_string ("  " ^ name ^ ": ");
                         Id.print id';
                         if Hashtbl.mem ValueAnalysis.tbl (V_Name id') then
                           Print.print_loc (ValueAnalysis.get (V_Name id')).loc;
                         print_newline ())))
end

module Current = struct
  let cmtModName : string ref = ref ""
end

let markValuesAffectSideEffect e =
  match e.exp_desc with
  | Texp_setfield (exp1, lid, ld, exp2) ->
    ValueAnalysis.joinLive (Value.expr exp1) Live.Top;
    ValueAnalysis.joinLive (Value.expr exp2) Live.Top
  | Texp_apply (exp, (_, Some _) :: _) ->
    if ValueAnalysis.isSideEffectFn (Value.expr exp) then
      ValueAnalysis.joinLive (Value.expr exp) Live.Top
  | Texp_ifthenelse (exp1, exp2, Some exp3) ->
    if ValueAnalysis.hasSideEffect exp2 || ValueAnalysis.hasSideEffect exp3 then
      ValueAnalysis.joinLive (Value.expr exp1) Live.Top
  | Texp_ifthenelse (exp1, exp2, None) ->
    if ValueAnalysis.hasSideEffect exp2 then
      ValueAnalysis.joinLive (Value.expr exp1) Live.Top
  | Texp_while (exp1, exp2) ->
    if ValueAnalysis.hasSideEffect exp2 then
      ValueAnalysis.joinLive (Value.expr exp1) Live.Top
  | Texp_for (id, pat, exp1, exp2, direction_flag, exp3) ->
    if ValueAnalysis.hasSideEffect exp3 then
      ValueAnalysis.joinLive
        (V_Name (Id.create !Current.cmtModName id))
        Live.Top
  | Texp_match (exp, cases, exn_cases, partial) ->
    let casesHasSideEffect =
      cases
      |> List.fold_left
           (fun acc case -> ValueAnalysis.hasSideEffect case.c_rhs || acc)
           false
    in
    if casesHasSideEffect then
      let cond =
        cases
        |> List.fold_left
             (fun acc case -> Live.join acc (Live.controlledByPat case.c_lhs))
             Live.Bot
      in
      ValueAnalysis.joinLive (Value.expr exp) cond
  | _ -> ()

module ClosureAnalysis = struct
  open Closure

  let updated = ref false

  let addValue vm v =
    let u = (ValueAnalysis.get vm).closure |> VClosure.addValue v in
    updated := !updated || u

  let addVESet vm vs =
    let u = (ValueAnalysis.get vm).closure |> VClosure.addVESet vs in
    updated := !updated || u

  let find k = (ValueAnalysis.get k).closure.values

  let markSideEffect e =
    let u =
      (ValueAnalysis.get (Value.expr e)).closure |> VClosure.markSideEffect
    in
    updated := !updated || u

  let addReduction eid reduce =
    let u =
      (ValueAnalysis.get (V_Expr eid)).closure |> VClosure.addReduction reduce
    in
    updated := !updated || u

  let markPassedToUnknown vm =
    ValueAnalysis.joinLive vm Live.Top;
    let u = (ValueAnalysis.get vm).closure |> VClosure.markPassedToUnknown in
    updated := !updated || u

  let rec initBind pat e =
    match pat.pat_desc with
    | Tpat_var (id, l) ->
      addValue
        (V_Name (Id.create !Current.cmtModName id))
        (ValueExpression.expr e)
    | Tpat_alias (pat', id, l) ->
      addValue
        (V_Name (Id.create !Current.cmtModName id))
        (ValueExpression.expr e);
      initBind pat' e
    | _ -> ()

  let initValueBinding vb = initBind vb.vb_pat vb.vb_expr

  let initExpr e =
    match e.exp_desc with
    | Texp_ident (path, lid, vd) -> (
      match vd.val_kind with
      | Val_reg ->
        let ids = ModuleEnv.resolvePath !Current.cmtModName path in
        if IdSet.is_empty ids then addVESet (Value.expr e) VS_Top;
        ids
        |> IdSet.iter (fun id ->
               let vm = V_Name id in
               if Hashtbl.mem ValueAnalysis.tbl vm then
                 addValue (Value.expr e) (VE_Name id)
               else addVESet (Value.expr e) VS_Top)
      | Val_prim prim ->
        (* print_endline prim.prim_name; *)
        (* print_endline (string_of_int prim.prim_arity); *)
        addValue (Value.expr e) (VE_Prim prim))
    | Texp_constant _ -> ()
    | Texp_let (_, _, exp) -> addValue (Value.expr e) (ValueExpression.expr exp)
    | Texp_function {arg_label; param; cases; partial} ->
      addValue (Value.expr e) (VE_Fn (Expr.toId e, param))
    | Texp_apply (exp, args) -> (
      let args = args |> List.map snd in
      match args with
      | Some hd :: tl ->
        addReduction (Expr.toId e)
          (Reduce
             (Expr.toId exp, Expr.toId hd, tl |> List.map (Option.map Expr.toId)))
      | None :: tl ->
        addValue (Value.expr e)
          (VE_PartialApp (Expr.toId exp, tl |> List.map (Option.map Expr.toId)))
      | [] -> raise (RuntimeError "Unreachable: Empty apply"))
    | Texp_match (exp, cases, exn_cases, partial) ->
      cases @ exn_cases
      |> List.iter (fun case ->
             addValue (Value.expr e) (ValueExpression.expr case.c_rhs);
             initBind case.c_lhs exp)
    | Texp_try (exp, cases) ->
      addValue (Value.expr e) (ValueExpression.expr exp);
      cases
      |> List.iter (fun case ->
             addValue (Value.expr e) (ValueExpression.expr case.c_rhs))
    | Texp_tuple exps ->
      exps
      |> List.iteri (fun i exp ->
             addValue (Value.expr e) (VE_Field (F_Tuple i, Expr.toId exp)))
    | Texp_construct (lid, cstr_desc, exps) ->
      addValue (Value.expr e) (VE_Cstr (cstr_desc, exps |> List.map Expr.toId))
    | Texp_variant (label, Some exp) ->
      addValue (Value.expr e) (VE_Variant (label, Expr.toId exp))
    | Texp_record {fields; representation; extended_expression} ->
      fields
      |> Array.iter (fun (label_desc, label_def) ->
             match label_desc.lbl_mut with
             | Immutable -> (
               match label_def with
               | Kept t -> ()
               | Overridden (lid, fe) ->
                 addValue (Value.expr e)
                   (VE_Field (F_Record label_desc.lbl_name, Expr.toId fe)))
             | Mutable -> (
               match label_def with
               | Kept t -> ()
               | Overridden (lid, fe) ->
                 addValue (Value.expr e)
                   (VE_Mutable (Expr.toId e, label_desc.lbl_name));
                 addValue
                   (V_Mutable (Expr.toId e, label_desc.lbl_name))
                   (ValueExpression.expr fe)))
    | Texp_field _ -> ()
    | Texp_setfield (exp1, lid, ld, exp2) -> markSideEffect e
    | Texp_array _ -> ()
    | Texp_ifthenelse (e1, e2, Some e3) ->
      addValue (Value.expr e) (ValueExpression.expr e2);
      addValue (Value.expr e) (ValueExpression.expr e3)
    | Texp_sequence (e1, e2) ->
      addValue (Value.expr e) (ValueExpression.expr e2)
    | Texp_while _ -> ()
    | Texp_for _ -> ()
    | _ -> markSideEffect e

  let initMapper =
    let super = CL.Tast_mapper.default in
    let expr self e =
      initExpr e;
      super.expr self e
    in
    let value_binding self vb =
      initValueBinding vb;
      super.value_binding self vb
    in
    {super with expr; value_binding}

  let rec bindUnknown cmtModName pat =
    let bindUnknown = bindUnknown cmtModName in
    match pat.pat_desc with
    | Tpat_any -> ()
    | Tpat_var (id, l) -> addVESet (V_Name (Id.create cmtModName id)) VS_Top
    | Tpat_alias (pat', id, l) ->
      addVESet (V_Name (Id.create cmtModName id)) VS_Top;
      bindUnknown pat'
    | Tpat_constant _ -> ()
    | Tpat_tuple pats -> pats |> List.iter bindUnknown
    | Tpat_construct (lid, cstr_desc, pats) -> pats |> List.iter bindUnknown
    | Tpat_variant (_, None, _) -> ()
    | Tpat_variant (lbl, Some pat, _) -> bindUnknown pat
    | Tpat_record (fields, _) ->
      fields |> List.iter (fun (_, _, pat') -> bindUnknown pat')
    | Tpat_or (pat1, pat2, _) ->
      bindUnknown pat1;
      bindUnknown pat2
    | Tpat_array pats -> pats |> List.iter bindUnknown
    | Tpat_lazy pat' -> bindUnknown pat'

  let update_transitivity vm =
    let passedToUnknown = (ValueAnalysis.get vm).closure.passedToUnknown in
    match find vm with
    | VS_Set s ->
      VESet.ElemSet.iter
        (fun v ->
          match v with
          | VE_Expr eid ->
            let set' = find (V_Expr eid) in
            addVESet vm set';
            if passedToUnknown then markPassedToUnknown (V_Expr eid)
          | VE_Name id ->
            let set' = find (V_Name id) in
            addVESet vm set';
            if passedToUnknown then markPassedToUnknown (V_Name id)
          | VE_Cstr (_, eids) ->
            if passedToUnknown then
              eids |> List.iter (fun eid -> markPassedToUnknown (V_Expr eid))
          | VE_Field (_, eid) ->
            if passedToUnknown then markPassedToUnknown (V_Expr eid)
          | VE_Mutable (eid, f) ->
            if passedToUnknown then markPassedToUnknown (V_Mutable (eid, f))
          | VE_Fn (eid, param) ->
            let bodies = bodyOfFunction eid in
            bodies
            |> List.iter (fun body -> bindUnknown body.cmtModName body.pat)
          | _ -> ())
        s
    | VS_Top -> ()

  let resolvePrimApp (prim : CL.Primitive.description) e app =
    match prim.prim_name with
    | "%addint" -> ()
    | _ ->
      let (Reduce (eid, arg1, args)) = app in
      addVESet (Value.expr e) VS_Top;
      ValueAnalysis.joinLive (V_Expr eid) Live.Top;
      Some arg1 :: args
      |> List.iter (function
           | None -> ()
           | Some eid -> ValueAnalysis.joinLive (V_Expr eid) Live.Top);
      markPassedToUnknown (V_Expr eid);
      markSideEffect e

  let rec patIsTop cmtModName pat =
    let patIsTop = patIsTop cmtModName in
    match pat.pat_desc with
    | Tpat_var (id, l) -> addVESet (V_Name (Id.create cmtModName id)) VS_Top
    | Tpat_alias (pat', id, l) ->
      addVESet (V_Name (Id.create cmtModName id)) VS_Top;
      patIsTop pat'
    | Tpat_or (pat1, pat2, _) ->
      patIsTop pat1;
      patIsTop pat2
    | Tpat_construct (_, _, pats) -> pats |> List.iter patIsTop
    | Tpat_variant (_, Some pat', _) -> patIsTop pat'
    | Tpat_tuple pats -> pats |> List.iter patIsTop
    | Tpat_array pats -> pats |> List.iter patIsTop
    | Tpat_lazy pat' -> patIsTop pat'
    | Tpat_record (fields, _) ->
      fields |> List.iter (fun (_, _, pat') -> patIsTop pat')
    | _ -> ()

  let rec stepBind cmtModName pat expr =
    let stepBind = stepBind cmtModName in
    match pat.pat_desc with
    | Tpat_any -> ()
    | Tpat_var (id, l) ->
      addValue (V_Name (Id.create cmtModName id)) (ValueExpression.expr expr)
    | Tpat_alias (pat', id, l) ->
      addValue (V_Name (Id.create cmtModName id)) (ValueExpression.expr expr);
      stepBind pat' expr
    | Tpat_constant _ -> ()
    | Tpat_tuple pats -> (
      match find (Value.expr expr) with
      | VS_Top -> pats |> List.iter (patIsTop cmtModName)
      | VS_Set vs ->
        vs
        |> VESet.ElemSet.iter (function
             | VE_Field (F_Tuple i, eid) ->
               stepBind (List.nth pats i) (Expr.fromId eid)
             | _ -> ()))
    | Tpat_construct (lid, cstr_desc, pats) -> (
      match find (Value.expr expr) with
      | VS_Top -> pats |> List.iter (patIsTop cmtModName)
      | VS_Set vs ->
        vs
        |> VESet.ElemSet.iter (fun v ->
               match v with
               | VE_Cstr (cstr_desc', eids) when cstr_desc = cstr_desc' ->
                 List.combine pats eids
                 |> List.iter (fun (pat, eid) -> stepBind pat (Expr.fromId eid))
               | _ -> ()))
    | Tpat_variant (_, None, _) -> ()
    | Tpat_variant (lbl, Some pat, _) -> (
      match find (Value.expr expr) with
      | VS_Top -> patIsTop cmtModName pat
      | VS_Set vs ->
        vs
        |> VESet.ElemSet.iter (function
             | VE_Variant (lbl', eid) when lbl = lbl' ->
               stepBind pat (Expr.fromId eid)
             | _ -> ()))
    | Tpat_record (fields, closed_flag) -> (
      match find (Value.expr expr) with
      | VS_Top ->
        fields |> List.iter (fun (_, _, pat) -> patIsTop cmtModName pat)
      | VS_Set vs ->
        vs
        |> VESet.ElemSet.iter (function
             | VE_Field (F_Record lbl, eid) ->
               fields
               |> List.iter (fun (lid, lbl_desc, pat) ->
                      if lbl_desc.lbl_name = lbl then
                        stepBind pat (Expr.fromId eid))
             | _ -> ()))
    | Tpat_or (pat1, pat2, _) ->
      stepBind pat1 expr;
      stepBind pat2 expr
    | Tpat_array _ -> () (* TODO: array *)
    | Tpat_lazy _ -> ()

  let stepExpr e =
    match e.exp_desc with
    | Texp_let (ref_flag, vbs, exp) ->
      let valueBindingsHaveSideEffect =
        vbs
        |> List.fold_left
             (fun acc vb -> acc || ValueAnalysis.hasSideEffect vb.vb_expr)
             false
      in
      if valueBindingsHaveSideEffect || ValueAnalysis.hasSideEffect exp then
        markSideEffect e
    | Texp_apply _ ->
      (ValueAnalysis.get (Value.expr e)).closure.reductions
      |> ReductionSet.elements
      |> List.iter (fun app ->
             match app with
             | Reduce (eid, arg, tl) -> (
               if ValueAnalysis.isSideEffectFn (V_Expr eid) then
                 markSideEffect e;
               match find (V_Expr eid) with
               | VS_Top ->
                 markSideEffect e;
                 addVESet (Value.expr e) VS_Top;
                 Some arg :: tl
                 |> List.iter (function
                      | None -> ()
                      | Some arg ->
                        ValueAnalysis.joinLive (V_Expr arg) Live.Top;
                        markPassedToUnknown (V_Expr arg))
               | VS_Set s ->
                 s
                 |> VESet.ElemSet.iter (fun v ->
                        match v with
                        | VE_Prim prim ->
                          if
                            tl |> List.for_all Option.is_some
                            && (tl |> List.length) + 1 = prim.prim_arity
                          then resolvePrimApp prim e app
                          else ()
                        | VE_Fn (eid, param) -> (
                          let bodies = bodyOfFunction eid in
                          bodies
                          |> List.iter (fun body ->
                                 stepBind body.cmtModName body.pat
                                   (Expr.fromId arg));
                          match tl with
                          | [] ->
                            bodies
                            |> List.iter (fun body ->
                                   addValue (Value.expr e) (VE_Expr body.exp_id))
                          | Some arg' :: tl' ->
                            bodies
                            |> List.iter (fun body ->
                                   addReduction (Expr.toId e)
                                     (Reduce (body.exp_id, arg', tl')))
                          | None :: tl' ->
                            bodies
                            |> List.iter (fun body ->
                                   addValue (Value.expr e)
                                     (VE_PartialApp (body.exp_id, tl'))))
                        | _ -> ())))
    | Texp_match (exp, cases, exn_cases, partial) ->
      cases
      |> List.iter (fun case -> stepBind !Current.cmtModName case.c_lhs exp);
      let casesHasSideEffect =
        cases @ exn_cases
        |> List.fold_left
             (fun acc case -> acc || ValueAnalysis.hasSideEffect case.c_rhs)
             false
      in
      if casesHasSideEffect then markSideEffect e
    | Texp_field (exp, lid, ld) -> (
      match find (Value.expr exp) with
      | VS_Top -> ()
      | VS_Set vs ->
        vs
        |> VESet.ElemSet.iter (function
             | VE_Field (f, eid) when Field.F_Record ld.lbl_name = f ->
               addValue (Value.expr exp) (VE_Expr eid)
             | _ -> ()))
    | Texp_setfield (exp1, lid, ld, exp2) -> (
      match find (Value.expr exp1) with
      | VS_Top -> ()
      | VS_Set vs ->
        vs
        |> VESet.ElemSet.iter (function
             | VE_Mutable (eid, f) when ld.lbl_name = f ->
               addValue (V_Mutable (eid, f)) (ValueExpression.expr exp2)
             | _ -> ()))
    | Texp_function {arg_label; param; cases; partial} ->
      let bodyHasSideEffect =
        cases
        |> List.fold_left
             (fun acc case -> acc || ValueAnalysis.hasSideEffect case.c_rhs)
             false
      in
      if bodyHasSideEffect then addValue (Value.expr e) VE_FnSideEffect
    | Texp_ifthenelse (exp1, exp2, Some exp3) ->
      if
        ValueAnalysis.hasSideEffect exp1
        || ValueAnalysis.hasSideEffect exp2
        || ValueAnalysis.hasSideEffect exp3
      then markSideEffect e
    | Texp_sequence (exp1, exp2) ->
      if ValueAnalysis.hasSideEffect exp1 || ValueAnalysis.hasSideEffect exp2
      then markSideEffect e
    | Texp_while (exp1, exp2) ->
      if ValueAnalysis.hasSideEffect exp1 || ValueAnalysis.hasSideEffect exp2
      then markSideEffect e
    | Texp_for (id, pat, exp1, exp2, df, exp3) ->
      if
        exp1 |> ValueAnalysis.hasSideEffect
        || exp2 |> ValueAnalysis.hasSideEffect
        || exp3 |> ValueAnalysis.hasSideEffect
      then markSideEffect e
    | _ -> ()

  let stepMapper =
    let super = CL.Tast_mapper.default in
    let expr self e =
      stepExpr e;
      super.expr self e
    in
    let value_binding self vb =
      stepBind !Current.cmtModName vb.vb_pat vb.vb_expr;
      super.value_binding self vb
    in
    {super with expr; value_binding}

  let runStructures strs =
    print_endline "############ closure init ##############";
    strs
    |> List.iter (fun (modname, str) ->
           Current.cmtModName := modname;
           initMapper.structure initMapper str |> ignore);
    updated := true;
    let counter = ref 0 in
    print_endline "############ closure step ##############";
    while !updated do
      counter := !counter + 1;
      Printf.printf "step %d" !counter;
      print_newline ();
      updated := false;
      ValueAnalysis.tbl |> Hashtbl.iter (fun vm _ -> update_transitivity vm);
      strs
      |> List.iter (fun (modname, str) ->
             Current.cmtModName := modname;
             stepMapper.structure stepMapper str |> ignore)
    done;
    print_endline "############ closure end ##############"
end

let traverseTopMostExprMapper (f : expression -> bool) =
  let super = CL.Tast_mapper.default in
  let expr self e = if f e then e else super.expr self e in
  {super with expr}

let collectDeadValues cmts =
  let deads = ref ValueSet.empty in
  let isDeadExpr e =
    let isDead =
      (ValueAnalysis.get (Value.expr e)).liveness = Live.Bot
      && not (ValueAnalysis.hasSideEffect e)
    in
    if isDead then deads := !deads |> ValueSet.add (Value.expr e);
    isDead
  in
  let mapper = traverseTopMostExprMapper isDeadExpr in
  cmts
  |> List.iter (fun (modname, str) -> mapper.structure mapper str |> ignore);
  ValueAnalysis.tbl
  |> Hashtbl.iter (fun vm _ ->
         match vm with
         | V_Name name ->
           if (ValueAnalysis.get vm).liveness = Live.Bot then
             deads := !deads |> ValueSet.add vm
         | _ -> ());
  !deads

module ValueDependencyAnalysis = struct
  let addEdge a b f =
    (* print_string "addEdge "; *)
    (* Value.print a; *)
    (* print_string " -> "; *)
    (* Value.print b; *)
    (* print_newline (); *)
    (* Current.graph |> Graph.addEdge a b f; *)
    ValueAnalysis.addDependency a b f

  let ( >> ) f g x = g (f x)

  module Func = struct
    let ifnotbot l : Live.t -> Live.t =
     fun x -> if Live.equal x Live.Bot then Live.Bot else l

    let iftop l : Live.t -> Live.t =
     fun x -> if Live.equal x Live.Top then l else Live.Bot

    let id : Live.t -> Live.t = fun x -> x
  end

  let collectPrimApp (prim : CL.Primitive.description) e app =
    let (Reduce (eid, eid2, args)) = app in
    match prim.prim_name with
    | _ ->
      addEdge (Value.expr e) (V_Expr eid) (Func.ifnotbot Live.Top);
      Some eid2 :: args
      |> List.fold_left
           (fun acc argo ->
             match argo with None -> acc | Some eid -> eid :: acc)
           []
      |> List.iter (fun eid ->
             addEdge (Value.expr e) (V_Expr eid) (Func.ifnotbot Live.Top))

  let rec collectBind cmtModName pat expr (f : Live.t -> Live.t) =
    let collectBind = collectBind cmtModName in
    match pat.pat_desc with
    | Tpat_var (id, l) ->
      addEdge (V_Name (Id.create cmtModName id)) (Value.expr expr) f
    | Tpat_alias (pat, id, l) ->
      addEdge (V_Name (Id.create cmtModName id)) (Value.expr expr) f;
      collectBind pat expr f
    | Tpat_tuple pats ->
      pats
      |> List.iteri (fun i pat ->
             collectBind pat expr (Live.field (F_Tuple i) >> f))
    | Tpat_construct (lid, cstr_desc, pats) ->
      pats
      |> List.iteri (fun i pat ->
             collectBind pat expr (Live.constructi cstr_desc i >> f))
    | Tpat_variant (lbl, None, row) -> ()
    | Tpat_variant (lbl, Some pat, row) ->
      collectBind pat expr (Option.some >> Live.variant lbl >> f)
    | Tpat_record (fields, closed_flag) ->
      fields
      |> List.iter (fun (lid, label_desc, pat) ->
             collectBind pat expr
               (Live.field (F_Record label_desc.lbl_name) >> f))
    | Tpat_array pats ->
      pats
      |> List.iter (fun pat -> collectBind pat expr (Func.ifnotbot Live.Top))
    | Tpat_or (pat1, pat2, _) ->
      collectBind pat1 expr f;
      collectBind pat2 expr f
    | Tpat_lazy pat -> collectBind pat expr (Func.ifnotbot Live.Top)
    | Tpat_any -> ()
    | Tpat_constant _ -> ()

  let collectExpr e =
    match e.exp_desc with
    | Texp_ident (path, lid, vd) ->
      let ids = ModuleEnv.resolvePath !Current.cmtModName path in
      ids
      |> IdSet.iter (fun id ->
             if Hashtbl.mem ValueAnalysis.tbl (V_Name id) then
               addEdge (Value.expr e) (V_Name id) Func.id)
    | Texp_constant _ -> ()
    | Texp_let (_, vbs, exp) -> addEdge (Value.expr e) (Value.expr exp) Func.id
    | Texp_function {arg_label; param; cases; partial} ->
      cases
      |> List.iter (fun case ->
             addEdge (Value.expr e) (Value.expr case.c_rhs)
               (Func.ifnotbot Live.Top);
             addEdge (Value.expr e) (Value.expr case.c_rhs)
               (Func.iftop Live.Top))
    | Texp_apply (exp, args) ->
      addEdge (Value.expr e) (Value.expr exp) (Func.ifnotbot Live.Top);
      (ValueAnalysis.get (Value.expr e)).closure.reductions
      |> ReductionSet.elements
      |> List.iter (fun app ->
             let (Reduce (eid, arg, tl)) = app in
             match (ValueAnalysis.get (V_Expr eid)).closure.values with
             | VS_Top -> ()
             | VS_Set s ->
               s
               |> VESet.ElemSet.iter (fun v ->
                      match v with
                      | VE_Prim prim ->
                        if
                          tl |> List.for_all Option.is_some
                          && (tl |> List.length) + 1 = prim.prim_arity
                        then collectPrimApp prim e app
                      | VE_Fn (eid, param) ->
                        let bodies = bodyOfFunction eid in
                        addEdge (Value.expr e) (V_Expr eid)
                          (Func.ifnotbot Live.Top);
                        bodies
                        |> List.iter (fun body ->
                               addEdge (Value.expr e) (V_Expr body.exp_id)
                                 Func.id;
                               collectBind body.cmtModName body.pat
                                 (Expr.fromId arg) Func.id)
                      | _ -> ()))
    | Texp_match (exp, cases, exn_cases, _) ->
      cases @ exn_cases
      |> List.iter (fun case ->
             addEdge (Value.expr e) (Value.expr case.c_rhs) Func.id;
             match case.c_guard with
             | Some guard ->
               addEdge (Value.expr e) (Value.expr guard)
                 (Func.ifnotbot Live.Top)
             | None -> ());
      let cond_base =
        cases
        |> List.map (fun case -> Live.controlledByPat case.c_lhs)
        |> List.fold_left Live.join Live.Bot
      in
      cases
      |> List.iter (fun case ->
             collectBind !Current.cmtModName case.c_lhs exp Func.id);
      addEdge (Value.expr e) (Value.expr exp) (Func.ifnotbot cond_base)
    | Texp_try (exp, cases) ->
      addEdge (Value.expr e) (Value.expr exp) Func.id;
      cases
      |> List.iter (fun case ->
             addEdge (Value.expr e) (Value.expr case.c_rhs) Func.id;
             match case.c_guard with
             | Some guard ->
               addEdge (Value.expr e) (Value.expr guard)
                 (Func.ifnotbot Live.Top)
             | None -> ())
    | Texp_tuple exps ->
      exps
      |> List.iteri (fun i exp ->
             addEdge (Value.expr e) (Value.expr exp)
               (Live.field_inv (F_Tuple i)))
    | Texp_construct (lid, cstr_desc, exps) ->
      assert (List.length exps = cstr_desc.cstr_arity);
      exps
      |> List.iteri (fun i exp ->
             addEdge (Value.expr e) (Value.expr exp)
               (Live.construct_inv cstr_desc i))
    | Texp_variant (label, None) -> ()
    | Texp_variant (label, Some exp) ->
      addEdge (Value.expr e) (Value.expr exp) (Live.variant_inv label)
    | Texp_record {fields; representation; extended_expression} ->
      fields
      |> Array.iter (fun (label_desc, label_def) ->
             match label_def with
             | Kept _ -> ()
             | Overridden (lid, fe) -> (
               match label_desc.lbl_mut with
               | Immutable ->
                 addEdge (Value.expr e) (Value.expr fe)
                   (Live.field_inv (F_Record label_desc.lbl_name))
               | Mutable ->
                 addEdge
                   (Value.mutableField e label_desc.lbl_name)
                   (Value.expr fe) Func.id))
    | Texp_field (exp, lid, ld) ->
      addEdge (Value.expr e) (Value.expr exp)
        (Live.field (F_Record ld.lbl_name))
    | Texp_setfield (exp1, lid, label_desc, exp2) -> (
      match (ValueAnalysis.get (Value.expr exp1)).closure.values with
      | VS_Top -> ()
      | VS_Set vs ->
        vs
        |> VESet.ElemSet.iter (fun v ->
               match v with
               | VE_Mutable (eid, fieldname)
                 when label_desc.lbl_name = fieldname ->
                 addEdge (V_Mutable (eid, fieldname)) (Value.expr exp2) Func.id
               | _ -> ()))
    | Texp_array exps ->
      exps
      |> List.iter (fun exp ->
             addEdge (Value.expr e) (Value.expr exp) (Func.ifnotbot Live.Top))
    | Texp_ifthenelse (exp1, exp2, Some exp3) ->
      addEdge (Value.expr e) (Value.expr exp1) (Func.ifnotbot Live.Top);
      addEdge (Value.expr e) (Value.expr exp2) Func.id;
      addEdge (Value.expr e) (Value.expr exp3) Func.id
    | Texp_ifthenelse _ -> ()
    | Texp_sequence (_, exp2) ->
      addEdge (Value.expr e) (Value.expr exp2) Func.id
    | Texp_while _ -> ()
    | Texp_for (id, ppat, exp1, exp2, dir_flag, exp_body) ->
      addEdge
        (V_Name (Id.create !Current.cmtModName id))
        (Value.expr exp1) Func.id;
      addEdge
        (V_Name (Id.create !Current.cmtModName id))
        (Value.expr exp2) Func.id
    | Texp_send (exp, meth, expo) ->
      addEdge (Value.expr e) (Value.expr exp) (Func.ifnotbot Live.Top)
    | _ -> ()

  let collectMapper =
    let super = CL.Tast_mapper.default in
    let expr self e =
      collectExpr e;
      super.expr self e
    in
    let value_binding self vb =
      collectBind !Current.cmtModName vb.vb_pat vb.vb_expr Func.id;
      super.value_binding self vb
    in
    {super with expr; value_binding}
end

let rec getSignature (moduleType : CL.Types.module_type) =
  match moduleType with
  | Mty_signature signature -> signature
  | Mty_functor _ -> (
    match moduleType |> Compat.getMtyFunctorModuleType with
    | Some (_, mt) -> getSignature mt
    | _ -> [])
  | _ -> []

let processStructureItem ~moduleId structureItem =
  let rec bindMember moduleId (pat : pattern) =
    let newVar id loc te =
      ModuleEnv.addMember moduleId id;
      ValueAnalysis.addId id loc te
    in
    match pat.pat_desc with
    | Tpat_var (id, l) ->
      newVar (Id.create !Current.cmtModName id) l.loc pat.pat_type
    | Tpat_alias (p, id, l) ->
      newVar (Id.create !Current.cmtModName id) l.loc pat.pat_type;
      bindMember moduleId p
    | Tpat_tuple ps -> ps |> List.iter (bindMember moduleId)
    | Tpat_construct (_, _, ps) -> ps |> List.iter (bindMember moduleId)
    | Tpat_variant (_, Some p, _) -> bindMember moduleId p
    | Tpat_record (fs, _) ->
      fs |> List.iter (fun (_, _, p) -> bindMember moduleId p)
    | Tpat_array ps -> ps |> List.iter (bindMember moduleId)
    | Tpat_or (p1, p2, _) ->
      bindMember moduleId p1;
      bindMember moduleId p2
    | Tpat_lazy p -> bindMember moduleId p
    | _ -> ()
  in
  match structureItem.str_desc with
  | Tstr_value (_, vbs) ->
    vbs |> List.iter (fun vb -> bindMember moduleId vb.vb_pat)
  | _ -> ()

let processStructure ~moduleId structure =
  structure.str_items |> List.iter (processStructureItem ~moduleId)

let rec processSignatureItem ~moduleId (si : CL.Types.signature_item) =
  match si with
  | Sig_value _ ->
    (* print_endline "Sig_value"; *)
    let id, loc, kind, valType = si |> Compat.getSigValue in
    let id = Id.create !Current.cmtModName id in
    (* Id.print moduleId; *)
    (* print_string " -> "; *)
    (* Id.print id; *)
    (* print_newline (); *)
    ModuleEnv.addMember moduleId id;
    ValueAnalysis.addId id loc valType
  | Sig_module _ -> (
    (* print_endline "Sig_module"; *)
    match si |> Compat.getSigModuleModtype with
    | Some (id, moduleType, moduleLoc) ->
      let id = Id.create !Current.cmtModName id in
      ModuleEnv.addMember moduleId id;
      let signature = getSignature moduleType in
      processSignature ~moduleId:id signature
    | None -> ())
  | _ -> ()

and processSignature ~moduleId (signature : CL.Types.signature) =
  signature
  |> List.iter (fun sig_item -> processSignatureItem ~moduleId sig_item)

let rec processModuleExpr ~moduleId module_expr =
  match module_expr.mod_desc with
  | Tmod_structure structure -> processStructure ~moduleId structure
  | Tmod_constraint (me, _, _, _) -> processModuleExpr ~moduleId me
  | _ -> ()

let annotatedAsLive attributes =
  attributes
  |> Annotation.getAttributePayload (( = ) DeadCommon.liveAnnotation)
  <> None

let preprocessFunction e =
  let eid = Expr.toId e in
  match e.exp_desc with
  | Texp_function {param; cases} ->
    let ids =
      cases
      |> List.map (fun case ->
             {
               cmtModName = !Current.cmtModName;
               pat = case.c_lhs;
               exp_id = Expr.toId case.c_rhs;
             })
    in
    if Hashtbl.mem idToBody eid then raise (RuntimeError "duplicate ident");
    Hashtbl.add idToBody eid ids
  | _ -> ()

let rec iterIdInPat f (pat : pattern) =
  let r = iterIdInPat f in
  match pat.pat_desc with
  | Tpat_var (id, _) -> f id
  | Tpat_alias (p, id, _) ->
    f id;
    r p
  | Tpat_tuple ps -> ps |> List.iter r
  | Tpat_construct (_, _, ps) -> ps |> List.iter r
  | Tpat_variant (_, Some p, _) -> p |> r
  | Tpat_record (fs, _) -> fs |> List.iter (fun (_, _, p) -> r p)
  | Tpat_array ps -> ps |> List.iter r
  | Tpat_or (p1, p2, _) ->
    r p1;
    r p2
  | Tpat_lazy p -> r p
  | Tpat_any _ -> ()
  | Tpat_variant _ -> ()
  | Tpat_constant _ -> ()

let preprocessMapper =
  let super = CL.Tast_mapper.default in
  let pat self p =
    (match p.pat_desc with
    | Tpat_var (id, l) ->
      ValueAnalysis.addId (Id.create !Current.cmtModName id) l.loc p.pat_type
    | Tpat_alias (_, id, l) ->
      ValueAnalysis.addId (Id.create !Current.cmtModName id) l.loc p.pat_type
    | _ -> ());
    super.pat self p
  in
  let expr self e =
    let e = super.expr self e in
    let e' = Expr.preprocess e in
    ValueAnalysis.addExpr (Expr.toId e') e;
    preprocessFunction e';
    (match e'.exp_desc with
    | Texp_for (id, ppat, e1, _, _, _) ->
      ValueAnalysis.addId
        (Id.create !Current.cmtModName id)
        ppat.ppat_loc e1.exp_type
    | Texp_record {fields} ->
      fields
      |> Array.iter (fun (label_desc, _) ->
             match label_desc.lbl_mut with
             | Mutable ->
               ValueAnalysis.addMutableField (Expr.toId e') e' label_desc
             | Immutable -> ())
    | _ -> ());
    e'
  in
  let value_binding self valueBinding =
    let ret = super.value_binding self valueBinding in
    if valueBinding.vb_attributes |> annotatedAsLive then
      valueBinding.vb_pat
      |> iterIdInPat (fun id ->
             ValueAnalysis.joinLive
               (V_Name (Id.create !Current.cmtModName id))
               Live.Top);
    ret
  in
  let module_binding self moduleBinding =
    (* Print.print_ident moduleBinding.mb_id; *)
    (* print_newline (); *)
    let id = Id.create !Current.cmtModName moduleBinding.mb_id in
    let signature = getSignature moduleBinding.mb_expr.mod_type in
    processSignature ~moduleId:id signature;
    processModuleExpr ~moduleId:id moduleBinding.mb_expr;
    super.module_binding self moduleBinding
  in
  {super with pat; expr; module_binding; value_binding}

(* collect structures from cmt *)
let targetCmtStructures : (string * structure) list ref = ref []

let processCmtStructure modname (structure : CL.Typedtree.structure) =
  (* print_endline "processCmtStructure"; *)
  (* print_endline modname; *)
  (* Print.print_structure structure; *)
  (* print_newline (); *)
  processStructure ~moduleId:(Id.createCmtModuleId modname) structure;
  let structure = preprocessMapper.structure preprocessMapper structure in
  targetCmtStructures := (modname, structure) :: !targetCmtStructures;
  (* let _ = Print.print_structure structure in *)
  ()

let processCmt (cmt_infos : CL.Cmt_format.cmt_infos) =
  Current.cmtModName := cmt_infos.cmt_modname;
  let moduleId = Id.createCmtModuleId !Current.cmtModName in
  match cmt_infos.cmt_annots with
  (* .cmti *)
  | Interface signature -> processSignature ~moduleId signature.sig_type
  (* .cmt *)
  | Implementation structure ->
    processSignature ~moduleId structure.str_type;
    processCmtStructure cmt_infos.cmt_modname structure
  | _ -> ()

let reportDead ~ppf =
  print_endline "############ reportDead ##############";
  print_endline "################ Env #################";
  ModuleEnv.print ();
  (* init liveness *)
  print_endline "############ init liveness ##############";
  print_int (Hashtbl.length ValueAnalysis.tbl);
  (* print_newline (); *)
  (* print_int (Current.graph.nodes |> ValueSet.cardinal); *)
  print_newline ();
  (* closure analysis *)
  print_endline "############ closure analysis ##############";
  !targetCmtStructures |> ClosureAnalysis.runStructures;
  if !Common.Cli.debug then (
    print_endline "\n### Closure Analysis ###";
    (* Current.closure |> Closure.print; *)
    print_endline "\n### Reductions ###"
    (* Current.applications *)
    (* |> Hashtbl.iter (fun eid _ -> *)
    (*        Printf.printf "Expr(%s): " eid; *)
    (*        Current.applications |> Reductions.find eid |> ReductionSet.elements *)
    (*        |> Print.print_list *)
    (*             (function *)
    (*               | Reduce (eid, eid2, args) -> *)
    (*                 Printf.printf "App(%s,[" eid; *)
    (*                 Some eid2 :: args *)
    (*                 |> Print.print_list *)
    (*                      (fun arg -> *)
    (*                        match arg with *)
    (*                        | None -> print_string "-" *)
    (*                        | Some eid -> print_string eid) *)
    (*                      ","; *)
    (*                 print_string "])") *)
    (*             ", "; *)
    (*        print_newline ()) *));
  (* liveness by side effect *)
  let mapper =
    let super = CL.Tast_mapper.default in
    let expr self e =
      markValuesAffectSideEffect e;
      super.expr self e
    in
    {super with expr}
  in
  !targetCmtStructures
  |> List.iter (fun (modname, str) ->
         Current.cmtModName := modname;
         mapper.structure mapper str |> ignore);
  (* values dependencies *)
  print_endline
    "######################## Value Dependency #####################";
  let mapper = ValueDependencyAnalysis.collectMapper in
  !targetCmtStructures
  |> List.iter (fun (modname, str) ->
         Current.cmtModName := modname;
         mapper.structure mapper str |> ignore);
  (* tracking liveness *)
  print_endline
    "######################## Tracking Liveness #####################";
  let dag = ValueAnalysis.scc () in
  if !Common.Cli.debug then (
    print_endline "\n### Track liveness ###";
    print_endline "* Topological order:"
    (* dag *)
    (* |> List.iter (fun nodes -> *)
    (*        nodes |> Print.print_list Value.print ", "; *)
    (*        print_newline ()) *));
  let dependentsLives node =
    let dependents = (ValueAnalysis.get node).dependency.rev_adj in
    dependents
    |> List.fold_left
         (fun acc (dep, f) ->
           (ValueAnalysis.get dep).liveness |> f |> Live.join acc)
         Live.Bot
  in
  dag
  |> List.iter (fun nodes ->
         match nodes with
         | [] -> raise (RuntimeError "Empty SCC")
         | [node] ->
           (* Value.print node; *)
           ValueAnalysis.joinLive node (dependentsLives node)
         | _ ->
           nodes |> List.iter (fun node -> ValueAnalysis.joinLive node Live.Top)
         (* nodes |> List.iter (fun node -> Current.liveness |> Liveness.meet node (dependentsLives node)); *));
  (* log dead values *)
  if !Common.Cli.debug then print_endline "\n### Liveness, SideEffect ###"
    (* Current.liveness *)
    (* |> Hashtbl.iter (fun k v -> *)
    (*        Value.print k; *)
    (*        print_string ": "; *)
    (*        Live.print v; *)
    (*        (match k with *)
    (*        | VK_Expr eid -> *)
    (*          if ValueAnalysis.hasSideEffect (Expr.fromId eid) then *)
    (*            print_string ", φ" *)
    (*        | _ -> ()); *)
    (*        if (ValueAnalysis.get k).closure.passedToUnknown then print_string ", AoU"; *)
    (*        print_newline ()) *);
  print_endline "###########################################";
  print_endline "##                  DVA                  ##";
  print_endline "###########################################";
  let deadValues = collectDeadValues !targetCmtStructures in
  deadValues |> ValueSet.elements
  |> List.iter (function vm ->
         vm |> ValueAnalysis.get |> ValueAnalysis.report ppf);
  print_newline ()
