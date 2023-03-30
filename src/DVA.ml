open CL.Types
open CL.Typedtree

type expr_tag = CL.Location.t
type id = CL.Ident.t

let rec print_list pe del l =
  match l with
  | [] -> ()
  | [e] -> pe e
  | hd::tl -> pe hd; print_string del; print_list pe del tl

let string_of_loc (loc: CL.Location.t) =
  let (file, line, startchar) = CL.Location.get_pos_info loc.loc_start in
  let startchar =  startchar + 1 in 
  let endchar = loc.loc_end.pos_cnum - loc.loc_start.pos_cnum + startchar in
      Printf.sprintf "%i:%i:%i" line (startchar-1) (endchar-1)

module ValueVar = struct
  type t =
    | VV_Expr of expr_tag
    | VV_Mutable of expr_tag * string
    | VV_Var of id

  let compare = compare

  let print vv =
    match vv with
    | VV_Expr et -> Printf.printf "Expr(%s)" (string_of_loc et)
    | VV_Mutable (et, s) -> Printf.printf "Mut(%s)" s
    | VV_Var id -> Printf.printf "Var(%s)" id.name
end

module VVSet = Set.Make(ValueVar)


module Field = struct
  type t = F_Record of string | F_Tuple of int

  let compare = compare
end

module Value = struct
  type t =
    | V_Expr of expr_tag
    | V_Mutable of expr_tag * string
    | V_Var of id
    | V_Prim of CL.Primitive.description
    | V_Variant of string * expr_tag
    | V_Field of Field.t * expr_tag
    | V_Fn of id * expr_tag list (* λx.e *)
    | V_App of expr_tag * expr_tag option list (* e [_ e2 e3] *)
    | V_FnSideEffect

  let compare = compare

  let print v =
    match v with
    | V_Expr et -> Printf.printf "Expr(%s)" (string_of_loc et)
    | V_Mutable (et, s) -> Printf.printf "Mut(%s)" s
    | V_Var id -> Printf.printf "Var(%s)" id.name
    | V_Prim prim -> Printf.printf "Prim(%s)" prim.prim_name
    | V_Variant (k, et) -> Printf.printf "Variant(%s,%s)" k (string_of_loc et)
    | V_Field (f, et) -> Printf.printf "Field(%s,%s)" (match f with F_Record f -> f | F_Tuple n -> string_of_int n) (string_of_loc et)
    | V_Fn (param, ets) -> Printf.printf "Fn(%s)" param.name
    | V_App (et, etos) ->
        Printf.printf "App(%s,[" (string_of_loc et);
        etos |> print_list (fun eto ->
          match eto with
          | None -> print_string "-"
          | Some et -> print_string (string_of_loc et)
        ) ",";
        print_string "])"
    | V_FnSideEffect -> Printf.printf "λ.φ"
end
open Value
open ValueVar

module Application = struct
  type t = App of expr_tag * expr_tag option list
  let compare = compare
end
open Application

module AppSet = Set.Make (Application)

module Apps = struct
  type t = (expr_tag, AppSet.t) Hashtbl.t

  let add k app (apps: t): bool =
    match Hashtbl.find_opt apps k with
    | None -> Hashtbl.add apps k (AppSet.singleton app); true
    | Some s ->
        let s' = s |> AppSet.add app in
        if s' = s then false else (Hashtbl.replace apps k s'; true)

  let find k (apps: t) =
    match Hashtbl.find_opt apps k with
    | None -> AppSet.empty
    | Some s -> s
end

module StringMap = Map.Make (String)
module FieldMap = Map.Make (Field)

module Live = struct
  type t =
    | Top
    | Bot
    | Variant of (t option) StringMap.t
    | Record of t FieldMap.t

  let variant kappa l: t = Variant (StringMap.singleton kappa l)

  let record field l: t = Record (FieldMap.singleton field l)

  let rec join a b =
    match (a, b) with
    | Top, _ | _, Top -> Top
    | Bot, x | x, Bot -> x
    | Variant ks, Variant ks' ->
        let join_opt ao bo =
          match ao, bo with
          | Some a, Some b -> join a b
          | Some a, None -> a
          | None, Some b -> b
          | None, None -> Bot
        in
        Variant (StringMap.union (fun k l1 l2 -> Some (Some (join_opt l1 l2))) ks ks')
    | Record fs, Record fs' ->
        Record (FieldMap.union (fun k l1 l2 -> Some (join l1 l2)) fs fs')
    | _ -> Top

  let rec meet a b =
    match (a, b) with
    | Top, x | x, Top -> x
    | Bot, _ | _, Bot -> Bot
    | Variant ks, Variant ks' ->
        let meet_opt ao bo =
          match ao, bo with
          | Some a, Some b -> meet a b
          | _ -> Bot
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
    | _ -> Bot

  let kappa_inv k l =
    match l with
    | Top -> Top
    | Bot -> Bot
    | Variant ks -> (
        match StringMap.find_opt k ks with
        | None -> Bot
        | Some (Some l) -> l
        | Some None -> Bot
        )
    | Record fs -> Bot (* or error *)

  let field_inv k l =
    match l with
    | Top -> Top
    | Bot -> Bot
    | Variant fs -> Bot (* or error *)
    | Record fs -> (
        match FieldMap.find_opt k fs with None -> Bot | Some l -> l)

  let rec equal l1 l2 =
    match l1, l2 with
    | Top, Top -> true
    | Bot, Bot -> true
    | Variant ks1, Variant ks2 ->
        StringMap.equal (Option.equal equal) ks1 ks2
    | Record fs1, Record fs2 -> FieldMap.equal equal fs1 fs2
    | _ -> false


  let rec print l =
    let ps = print_string in
    match l with
    | Top -> ps "⊤"
    | Bot -> ps "⊥"
    | Variant ks ->
        ks
          |> StringMap.bindings
          |> print_list (fun (k, vo) ->
              ps k; ps "("; (match vo with Some(v) -> print v | None -> ()); ps ")") "+"
    | Record fs ->
        fs
          |> FieldMap.bindings
          |> print_list (fun (k, v) ->
              (match k with
              | Field.F_Tuple n -> print_int n
              | F_Record f -> print_string f
              );
              ps "("; print v; ps ")"
          ) "*"

  let rec baseFromPattern pat =
    match pat.pat_desc with
    | Tpat_alias (pat, id, l) -> baseFromPattern pat
    | Tpat_variant (label, pato, row) ->
        variant label (pato |> Option.map baseFromPattern)
    | Tpat_tuple pats ->
        pats |> List.mapi (fun i pat -> record (F_Tuple i) (baseFromPattern pat))
             |> List.fold_left (fun acc l -> join acc l) Bot
    | Tpat_constant c -> Top
    (* TODO *)
    | _ -> Bot
end

module ValueSet = struct
  module ElemSet = Set.Make (Value)

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
    | VS_Set s -> s |> ElemSet.elements |> print_list Value.print ", "

  let mem k vs =
    match vs with
    | VS_Top -> true
    | VS_Set s -> s |> ElemSet.mem k
end

module ValueMap = Map.Make (ValueVar)

module Closure = struct
  type t = (ValueVar.t, ValueSet.t) Hashtbl.t

  let addValue k v c: bool =
    match Hashtbl.find_opt c k with
    | None -> Hashtbl.add c k (ValueSet.singleton v); true
    | Some s ->
        let s' = ValueSet.add s v in
        if ValueSet.compare s s' = 0 then false else (Hashtbl.replace c k s'; true)

  let addValueSet k vs c =
    match Hashtbl.find_opt c k with
    | None -> Hashtbl.add c k vs; true
    | Some s ->
        let updated = not (ValueSet.subset vs s) in
        Hashtbl.replace c k (ValueSet.join s vs); updated

  let find k c =
    match Hashtbl.find_opt c k with None -> ValueSet.empty | Some s -> s

  let print c =
    c |> Hashtbl.to_seq |> Seq.iter (fun (vv, vs) ->
      ValueVar.print vv;
      print_string ": ";
      ValueSet.print vs;
      print_newline ())
end

module Liveness = struct
  type t = (ValueVar.t, Live.t) Hashtbl.t

  let init vvs liveness =
    vvs |> Seq.iter (fun vv -> Hashtbl.add liveness vv Live.Bot)

  let get k liveness =
    match Hashtbl.find_opt liveness k with
    | None -> Live.Bot
    | Some l -> l

  let join k l liveness =
    let l_prev = liveness |> get k in
    Hashtbl.replace liveness k (Live.join l l_prev)

  let meet k l liveness =
    let l_prev = liveness |> get k in
    Hashtbl.replace liveness k (Live.meet l l_prev)
end

module ExprTagSet = Set.Make (struct type t = expr_tag let compare = compare end)

module Stack = struct
  type 'a t = 'a list ref

  exception EmptyStack

  let create () = ref []

  let push x st = st := x::!st

  let pop st =
    match !st with
    | [] -> raise EmptyStack
    | hd::tl -> st := tl; hd

  let to_list st = !st
end


module Graph = struct
  type node = ValueVar.t
  type func = Live.t -> Live.t
  type adj_list = (node, (node * func)) Hashtbl.t

  type t = {mutable nodes: VVSet.t; adj: adj_list; adj_rev: adj_list;}

  let reset g =
    Hashtbl.reset g.adj;
    Hashtbl.reset g.adj_rev

  let addEdge (v1: node) (v2: node) f (g: t) =
    let {adj; adj_rev} = g in
    print_string "add edge: ";
    ValueVar.print v1;
    print_string " -> ";
    ValueVar.print v2;
    print_newline();
    Hashtbl.add adj v1 (v2, f);
    Hashtbl.add adj_rev v2 (v1, f)

  let scc (g: t): node list list =
    let counter = ref 0 in
    let stack = Stack.create () in
    let num = Hashtbl.create 256 in
    let getnum vv =
      match Hashtbl.find_opt num vv with
      | Some res -> res
      | None -> 0
    in
    let finished = ref VVSet.empty in
    let markfinished vv = finished := !finished |> VVSet.add vv in
    let isfinished vv = !finished |> VVSet.mem vv in
    let scc = Stack.create () in
    let rec dfs v =
      counter := !counter + 1;
      Hashtbl.add num v !counter;
      stack |> Stack.push v;
      let result =
        Hashtbl.find_all g.adj v
          |> List.fold_left (fun result (next, _) -> if getnum next = 0 then min result (dfs next) else if not (isfinished next) then min result (getnum next) else result) (getnum v)
      in
      if result = getnum v then (
        let nodes = Stack.create () in
        let break = ref false in
        while not !break do
          let t = stack |> Stack.pop in
          nodes |> Stack.push t;
          markfinished t;
          if ValueVar.compare t v = 0 then break := true
        done;
        scc |> Stack.push (nodes |> Stack.to_list);
      );
      result
    in
    g.nodes |> VVSet.iter (fun node -> if getnum node = 0 then dfs node |> ignore);
    scc |> Stack.to_list

end

module Current = struct
  let locToExpr : (CL.Location.t, expression) Hashtbl.t = Hashtbl.create 256

  let exprOfTag : expr_tag -> expression = function
    | tag -> Hashtbl.find locToExpr tag

  let closure : Closure.t = Hashtbl.create 256

  let sideEffectSet : ExprTagSet.t ref = ref ExprTagSet.empty

  let liveness : Liveness.t = Hashtbl.create 256

  let applications : Apps.t = Hashtbl.create 256

  let graph : Graph.t = {nodes = VVSet.empty; adj = Hashtbl.create 256; adj_rev = Hashtbl.create 256}

  let markSideEffect e: bool =
    if !sideEffectSet |> ExprTagSet.mem e.exp_loc then
      false
    else
      (sideEffectSet := !sideEffectSet |> ExprTagSet.add e.exp_loc;
      true)

  let hasSideEffect : expression -> bool = fun e ->
    !sideEffectSet |> ExprTagSet.mem e.exp_loc

  let isSideEffectFn : expression -> bool = fun e ->
    closure |> Closure.find (VV_Expr e.exp_loc) |> ValueSet.mem V_FnSideEffect

  let markValuesAffectSideEffect e =
    match e.exp_desc with
    | Texp_setfield (exp1, lid, ld, exp2) ->
        liveness |> Liveness.join (VV_Expr exp1.exp_loc) Live.Top;
        liveness |> Liveness.join (VV_Expr exp2.exp_loc) Live.Top
    | Texp_apply (exp, (_, Some (_))::_) ->
        if exp |> isSideEffectFn then
          liveness |> Liveness.join (VV_Expr exp.exp_loc) Live.Top
    | Texp_ifthenelse (exp1, exp2, Some (exp3)) ->
        if exp2 |> hasSideEffect || exp3 |> hasSideEffect then
          liveness |> Liveness.join (VV_Expr exp1.exp_loc) Live.Top
    | Texp_ifthenelse (exp1, exp2, None) ->
        if hasSideEffect exp2 then
          liveness |> Liveness.join (VV_Expr exp1.exp_loc) Live.Top
    | Texp_while (exp1, exp2) ->
        if exp2 |> hasSideEffect then
          liveness |> Liveness.join (VV_Expr exp1.exp_loc) Live.Top
    | Texp_for (id, pat, exp1, exp2, direction_flag, exp3) ->
        if exp3 |> hasSideEffect then
          liveness |> Liveness.join (VV_Var id) Live.Top
    | Texp_match (exp, cases, exn_cases, partial) ->
        let casesHasSideEffect = cases |> List.fold_left (fun acc case ->
          case.c_rhs |> hasSideEffect || acc) false
        in
        if casesHasSideEffect then
            let cond = cases |> List.fold_left (fun acc case ->
              Live.join acc (Live.baseFromPattern case.c_lhs)) Live.Bot
            in 
            liveness |> Liveness.join (VV_Expr exp.exp_loc) cond
    | _ -> ()

  let reset () =
    Hashtbl.reset locToExpr;
    Hashtbl.reset closure;
    sideEffectSet := ExprTagSet.empty;
    Hashtbl.reset applications;
    Graph.reset graph;
    Hashtbl.reset liveness
end

let traverseExpr (f : expression -> unit) e =
  let super = CL.Tast_mapper.default in
  let expr self e =
    f e;
    super.expr self e
  in
  let mapper = {super with expr} in
  let _ = mapper.expr mapper e in
  ()

let traverseValueVar f e =
  let rec traversePat pat =
    match pat.pat_desc with
    | Tpat_var (id, l) -> f (VV_Var id)
    | Tpat_alias (pat', id, l) -> f (VV_Var id); traversePat pat'
    | _ -> ()
  in
  e |> traverseExpr (fun e ->
    f (VV_Expr e.exp_loc);
    match e.exp_desc with
    | Texp_let (rec_flag, vbs, exp) ->
        vbs |> List.iter (fun vb -> traversePat vb.vb_pat)
    | Texp_function {arg_label; param; cases; partial} -> f (VV_Var param)
    | Texp_match (exp, cases, exn_cases, partial) ->
        cases |> List.iter (fun case -> traversePat case.c_lhs)
    | Texp_for (id, _, _, _, _, _) -> f (VV_Var id)
    | _ -> ()
  )

module ClosureAnalysis = struct
  open Closure

  let init e c =
    let rec bind pat e =
      match pat.pat_desc with
      | Tpat_var (id, l) -> c |> addValue (VV_Var id) (V_Expr e.exp_loc) |> ignore
      | Tpat_alias (pat', id, l) ->
        c |> addValue (VV_Var id) (V_Expr e.exp_loc) |> ignore;
        bind pat' e
      (* TODO *)
      | _ -> ()
    in
    match e.exp_desc with
    | Texp_ident (path, lid, vd) -> (
      match vd.val_kind with
      | Val_reg -> c |> addValue (VV_Expr e.exp_loc) (V_Var (CL.Path.head path)) |> ignore
      | Val_prim prim ->
        c |> addValue (VV_Expr e.exp_loc) (V_Prim prim) |> ignore
    )
    | Texp_function {arg_label; param; cases; partial} ->
      cases |> List.iter (fun case -> bind case.c_lhs case.c_rhs);
      let tags = cases |> List.map (fun case -> case.c_rhs.exp_loc) in
      c |> addValue (VV_Expr e.exp_loc) (V_Fn (param, tags)) |> ignore
    | Texp_let (rec_flag, vbs, exp) ->
      c |> addValue (VV_Expr e.exp_loc) (V_Expr exp.exp_loc) |> ignore;
      vbs |> List.iter (fun vb -> bind vb.vb_pat vb.vb_expr)
    | Texp_variant (label, Some exp) ->
      c |> addValue (VV_Expr e.exp_loc) (V_Variant (label, exp.exp_loc)) |> ignore
    | Texp_tuple exps ->
      exps
      |> List.iteri (fun i exp ->
             c |> addValue (VV_Expr e.exp_loc) (V_Field (F_Tuple i, exp.exp_loc)) |> ignore)
    | Texp_try (exp, cases) ->
      c |> addValue (VV_Expr e.exp_loc) (V_Expr exp.exp_loc) |> ignore;
      cases
      |> List.iter (fun case ->
             c |> addValue (VV_Expr e.exp_loc) (V_Expr case.c_rhs.exp_loc) |> ignore)
    | Texp_record {fields; representation; extended_expression} ->
      fields
      |> Array.iter (fun (label_desc, label_def) ->
             match label_desc.lbl_mut with
             | Immutable -> (
               match label_def with
               | Kept t -> () (* TODO *)
               | Overridden (lid, fe) ->
                   c |> addValue (VV_Expr e.exp_loc) (V_Field (F_Record label_desc.lbl_name, fe.exp_loc)) |> ignore
             )
             | Mutable -> (
               match label_def with
               | Kept t -> () (* TODO *)
               | Overridden (lid, fe) -> () (* TODO *)))
    | Texp_apply (exp, args) ->
      let arg_tags =
        args |> List.map snd |> List.map (Option.map (fun e -> e.exp_loc))
      in
      (match arg_tags with
      | (Some _)::_ -> Current.applications |> Apps.add e.exp_loc (App (exp.exp_loc, arg_tags)) |> ignore
      | _ -> c |> addValue (VV_Expr e.exp_loc) (V_App (exp.exp_loc, arg_tags)) |> ignore
      )
    | Texp_match (e, cases, exn_cases, partial) ->
      cases
      |> List.iter (fun case ->
             c |> addValue (VV_Expr e.exp_loc) (V_Expr case.c_rhs.exp_loc) |> ignore;
             bind case.c_lhs case.c_rhs)
    | Texp_sequence (e1, e2) ->
      c |> addValue (VV_Expr e.exp_loc) (V_Expr e2.exp_loc) |> ignore
    | Texp_ifthenelse (e1, e2, Some e3) ->
      c |> addValue (VV_Expr e.exp_loc) (V_Expr e2.exp_loc) |> ignore;
      c |> addValue (VV_Expr e.exp_loc) (V_Expr e3.exp_loc) |> ignore
    | Texp_setfield (exp1, lid, ld, exp2) ->
        Current.markSideEffect e |> ignore
    | _ -> ()

  let update_transitivity vv c =
    let set = c |> find vv in
    match set with
    | VS_Set s ->
      ValueSet.ElemSet.fold
        (fun v acc ->
          match v with
          | V_Expr et ->
            let set' = c |> find (VV_Expr et) in
            acc || c |> addValueSet vv set'
          | V_Var id ->
            let set' = c |> find (VV_Var id) in
            acc || c |> addValueSet vv set'
          | _ -> acc)
        s false
    | VS_Top -> false

  let resolvePrimApp (prim: CL.Primitive.description) e app =
    match prim.prim_name with
    | "%addint" -> false
    | _ ->
      match app with
      | App (tag, arg_tags) ->
          Current.liveness |> Liveness.join (VV_Expr tag) Live.Top;
          arg_tags |> List.iter (function None -> () | Some tag ->
            Current.liveness |> Liveness.join (VV_Expr tag) Live.Top);
          Current.markSideEffect e

  let step e c : bool =
    (* let updated = c |> update_transitivity (VV_Expr e.exp_loc) in *)
    let updated =
      match e.exp_desc with
      | Texp_let (ref_flag, vbs, exp) ->
          let valueBindingsHaveSideEffect =
            vbs |> List.fold_left (fun acc vb -> acc || vb.vb_expr |> Current.hasSideEffect) false
          in
            if valueBindingsHaveSideEffect || exp |> Current.hasSideEffect then
              Current.markSideEffect e
            else
              false
      | Texp_apply _ ->
          Current.applications
            |> Apps.find e.exp_loc
            |> AppSet.elements
            |> List.fold_left (fun acc app ->
                acc || match app with
                | App (tag, (Some arg)::tl) ->
                    (match c |> find (VV_Expr tag) with
                    | VS_Top -> c |> addValueSet (VV_Expr e.exp_loc) VS_Top
                    | VS_Set s -> acc |> ValueSet.ElemSet.fold (fun v acc ->
                        match v with
                        | V_Prim prim -> 
                            if tl |> List.for_all Option.is_some
                                && (tl |> List.length) + 1 = prim.prim_arity then
                              resolvePrimApp prim e app
                            else
                              false
                        | V_Fn (param, bodies) ->
                            let updated = c |> addValue (VV_Var param) (V_Expr arg) in
                            (match tl with
                            | [] ->
                              bodies |> List.fold_left (fun acc body ->
                                c |> addValue (VV_Expr e.exp_loc) (V_Expr body) || acc
                              ) updated
                            | (Some _)::tl' ->
                              bodies |> List.fold_left (fun acc body ->
                                Current.applications |> Apps.add e.exp_loc (App (body, tl)) || acc
                              ) updated
                            | None::tl' ->
                              bodies |> List.fold_left (fun acc body ->
                                c |> addValue (VV_Expr e.exp_loc) (V_App (body, tl)) || acc
                              ) updated
                            )
                        | _ -> acc
                        ) s
                    )
                | _ -> acc
                ) false
      | Texp_field (exp, lid, ld) ->
          let set = c |> find (VV_Expr exp.exp_loc) in
          (* TODO *)
          false
      | Texp_function {arg_label; param; cases; partial; } ->
          let bodyHasSideEffect =
            cases |> List.fold_left (fun acc case -> acc || case.c_rhs |> Current.hasSideEffect ) false
          in
          if bodyHasSideEffect then
            c |> addValue (VV_Expr e.exp_loc) V_FnSideEffect
          else
            false
      | Texp_ifthenelse (exp1, exp2, Some exp3) ->
          if exp1 |> Current.hasSideEffect
              || exp2 |> Current.hasSideEffect
              || exp3 |> Current.hasSideEffect then
            Current.markSideEffect e
          else
            false
      | Texp_sequence (exp1, exp2) ->
          if exp1 |> Current.hasSideEffect || exp2 |> Current.hasSideEffect then
            Current.markSideEffect e
          else
            false
      | Texp_while (exp1, exp2) ->
          if exp1 |> Current.hasSideEffect || exp2 |> Current.hasSideEffect then
            Current.markSideEffect e
          else
            false
      | Texp_for (id, pat, exp1, exp2, df, exp3) ->
          if exp1 |> Current.hasSideEffect
              || exp2 |> Current.hasSideEffect
              || exp3 |> Current.hasSideEffect then
            Current.markSideEffect e
          else
            false
      | _ -> false
    in
    updated

  let run e =
    e |> traverseExpr (fun e -> init e Current.closure);
    let updated = ref true in
    while !updated do
      updated := false;
      Current.graph.nodes |> VVSet.iter (fun vv -> updated := Current.closure |> update_transitivity vv || !updated);
      e |> traverseExpr (fun e -> updated := step e Current.closure || !updated)
    done
end

let collectValueVar e =
  let vvs = ref VVSet.empty in
  traverseValueVar (fun vv -> vvs := !vvs |> VVSet.add vv) e;
  !vvs

let traverseTopMostExpr (f : expression -> bool) e =
  let super = CL.Tast_mapper.default in
  let expr self e =
    if f e then e else super.expr self e
  in
  let mapper = {super with expr} in
  let _ = mapper.expr mapper e in
  ()

let collectDeadValues e =
  let deads = ref VVSet.empty in
  e |> traverseTopMostExpr (fun e ->
    let isDead =
      Current.liveness |> Liveness.get (VV_Expr e.exp_loc) = Live.Bot
      && not (Current.hasSideEffect e)
    in
    if isDead then deads := !deads |> VVSet.add (VV_Expr e.exp_loc);
    isDead
  );
  Current.graph.nodes |> VVSet.iter (fun vv ->
    match vv with
    | VV_Var id ->
        if Current.liveness |> Liveness.get vv = Live.Bot
        then deads := !deads |> VVSet.add vv
    | _ -> ()
  );
  !deads

let resolvePrimAppValueDependency (prim: CL.Primitive.description) e app =
  let App (tag, arg_tags) = app in
  match prim.prim_name with
  | _ -> 
      Current.graph |> Graph.addEdge (VV_Expr e.exp_loc) (VV_Expr tag) (fun x -> if Live.equal x Live.Bot then Live.Bot else Live.Top);
      arg_tags |> List.fold_left (fun acc o -> match o with None -> acc | Some v -> v::acc) []
        |> List.iter (fun et ->
            Current.graph |> Graph.addEdge (VV_Expr e.exp_loc) (VV_Expr et) (fun x -> if Live.equal x Live.Bot then Live.Bot else Live.Top))


let makeValueDependencies e =
  let rec bind pat expr =
    match pat.pat_desc with
    | Tpat_var (id, l) -> 
        Current.graph |> Graph.addEdge (VV_Var id) (VV_Expr expr.exp_loc) (fun x -> x)
    | Tpat_alias (pat, id, l) ->
        Current.graph |> Graph.addEdge (VV_Var id) (VV_Expr expr.exp_loc) (fun x -> x);
        bind pat expr
    | _ -> ()
  in
  match e.exp_desc with
  | Texp_ident (path, lid, vd) ->
      Current.graph |> Graph.addEdge (VV_Expr e.exp_loc) (VV_Var (CL.Path.head path)) (fun x -> x)
  | Texp_let (rec_flag, vbs, exp) ->
      Current.graph |> Graph.addEdge (VV_Expr e.exp_loc) (VV_Expr exp.exp_loc) (fun x -> x);
      vbs |> List.iter (fun vb -> bind vb.vb_pat vb.vb_expr)
  | Texp_function {arg_label; param; cases; partial; } -> ()
  | Texp_apply (exp, args) ->
      Current.applications
        |> Apps.find e.exp_loc
        |> AppSet.elements
        |> List.iter (fun app ->
            match app with
            | App (tag, (Some arg)::tl) ->
                (match Current.closure |> Closure.find (VV_Expr tag) with
                | VS_Top -> ()
                | VS_Set s -> s |> ValueSet.ElemSet.iter (fun v ->
                    match v with
                    | V_Prim prim -> 
                        if tl |> List.for_all Option.is_some
                            && (tl |> List.length) + 1 = prim.prim_arity then
                          resolvePrimAppValueDependency prim e app
                    | V_Fn (param, bodies) ->
                        Current.graph |> Graph.addEdge (VV_Var param) (VV_Expr arg) (fun x -> x);
                        Current.graph |> Graph.addEdge (VV_Expr e.exp_loc) (VV_Expr tag) (fun x -> if Live.equal x Live.Bot then Live.Bot else Live.Top);
                        bodies |> List.iter (fun body ->
                          Current.graph |> Graph.addEdge (VV_Expr e.exp_loc) (VV_Expr body) (fun x -> x)
                        )
                    | _ -> ()
                    )
                )
            | _ -> ()
            )
  | Texp_match (exp, cases, exn_cases, partial) ->
      cases |> List.iter (fun case ->
        Current.graph |> Graph.addEdge (VV_Expr e.exp_loc) (VV_Expr case.c_rhs.exp_loc) (fun x -> x));
      let base = cases |> List.fold_left (fun acc case -> Live.join acc (Live.baseFromPattern case.c_lhs)) Live.Bot in
      Current.graph |> Graph.addEdge (VV_Expr e.exp_loc) (VV_Expr exp.exp_loc) (fun x -> if Live.equal x Live.Bot then Live.Bot else base)
      

  | Texp_try (exp, cases) -> ()
  | Texp_tuple (exps) -> ()
  | Texp_variant (label, expo) -> ()
  | Texp_record {fields; representation; extended_expression;} ->
      fields |> Array.iter (fun (label_desc, label_def) ->
        match label_def with
        | Kept _ -> ()
        | Overridden (lid, fe) ->
            (match label_desc.lbl_mut with
            | Immutable -> Current.graph |> Graph.addEdge (VV_Expr e.exp_loc) (VV_Expr fe.exp_loc) (fun x -> Live.field_inv (F_Record label_desc.lbl_name) x)
            | Mutable -> ()
            )
      )
  | Texp_field (exp, lid, ld) ->
      Current.graph |> Graph.addEdge (VV_Expr e.exp_loc) (VV_Expr exp.exp_loc) (fun x -> Live.record (F_Record ld.lbl_name) x)
  | Texp_ifthenelse (exp1, exp2, exp3o) -> ()
  | Texp_sequence (exp1, exp2) -> ()
  | Texp_while (exp1, exp2) -> ()
  | Texp_for (id, pat, exp1, exp2, dir_flag, exp3) -> ()
  | _ -> ()

exception RuntimeError of string

let processExpression (e : CL.Typedtree.expression) =
  print_newline ();
  print_endline "===== Analyze ===== ";
  CL.Location.print_loc Format.std_formatter e.exp_loc;
  print_endline Log_.Color.reset_lit;
  Print.print_expression 0 e;
  print_newline();
  (* Preprocessing *)
  Current.reset ();
  e |> traverseExpr (fun e -> Hashtbl.add Current.locToExpr e.exp_loc e);
  Current.graph.nodes <- collectValueVar e;
  print_string "nodes: ";
  Current.graph.nodes |> VVSet.elements |> print_list ValueVar.print ", ";
  print_newline ();
  Current.liveness |> Liveness.init (Current.graph.nodes |> VVSet.to_seq);
  (* Closure Analysis *)
  print_endline "\n### Closure Analysis ###";
  ClosureAnalysis.run e;
  Current.closure |> Closure.print;
  print_endline "\n### Applications ###";
  Current.applications |> Hashtbl.iter (fun k _ ->
    Printf.printf "Expr(%s): " (string_of_loc k);
    (Current.applications |> Apps.find k |> AppSet.elements)
      |> print_list (function
        | App (tag, arg_tags) ->
            Printf.printf "App(%s,[" (string_of_loc tag);
            arg_tags |> print_list (fun arg ->
              match arg with
              | None -> print_string "-"
              | Some et -> print_string (string_of_loc et)
            ) ",";
            print_string "])"
      ) ", ";
    print_newline ()
  );
  (* live values by side effect *)
  e |> traverseExpr Current.markValuesAffectSideEffect;
  (* values dependencies *)
  print_endline "\n### Make value dependencies ###";
  e |> traverseExpr makeValueDependencies;
  (* Tracking liveness *)
  print_endline "\n### Track liveness ###";
  print_endline "* Topological order:";
  let dag = Graph.scc Current.graph in
  dag |> List.iter (fun nodes ->
    nodes |> print_list ValueVar.print ", "; print_newline ()
  );
  let dependentsLives node =
    let dependents = Hashtbl.find_all Current.graph.adj_rev node in
    dependents |> List.fold_left (fun acc (dep, f) ->
      Current.liveness |> Liveness.get dep |> f |> Live.join acc
    ) Live.Bot
  in
  dag |> List.iter (fun nodes ->
    
    match nodes with
    | [] -> raise (RuntimeError "Empty SCC")
    | [node] ->
        ValueVar.print node;
        Current.liveness |> Liveness.join node (dependentsLives node)
    | _ ->
        nodes |> List.iter (fun node -> Current.liveness |> Liveness.join node Live.Top)
        (* nodes |> List.iter (fun node -> Current.liveness |> Liveness.meet node (dependentsLives node)); *)
  );
  (* Log dead values *)
  print_endline "\n### Liveness, SideEffect ###";
  Current.liveness |> Hashtbl.iter (fun k v ->
    ValueVar.print k;
    print_string ": ";
    Live.print v;
    (match k with
    | VV_Expr et -> if !Current.sideEffectSet |> ExprTagSet.mem et then print_string ", φ"
    | _ -> ()
    );
    print_newline ()
  );
  print_endline "\n### Dead Codes ###";
  let deadValues = collectDeadValues e in
  deadValues
    |> VVSet.elements
    |> List.iter (function vv ->
        match vv with
        | VV_Expr et ->
            print_string "* ";
            ValueVar.print vv;
            print_newline ();
            let exp = Current.exprOfTag et in
            Print.print_expression 0 exp;
            print_newline ()
        | VV_Var id ->
            print_string "* ";
            ValueVar.print vv;
            print_newline ()
        | _ -> ())
  ;
  print_newline ()

let processStructureItem (structureItem : CL.Typedtree.structure_item) =
  match structureItem.str_desc with
  | Tstr_eval (expr, attr) -> processExpression expr
  | Tstr_value (rec_flag, valueBinding) -> ()
  | _ -> ()

let processStructure (structure : CL.Typedtree.structure) =
  let _ = Print.print_structure structure in
  structure.str_items |> List.iter processStructureItem
