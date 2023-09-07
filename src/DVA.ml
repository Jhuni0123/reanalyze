open SetExpression
open ClosureAnalysis
open CL.Typedtree
open CL.Types

module StringSet = Set.Make(String)

type cmt_structure = {modname : string; structure : structure; label : Label.t}

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

let annotatedAsLive attributes =
  attributes
  |> Annotation.getAttributePayload (( = ) DeadCommon.liveAnnotation)
  <> None

module ValueDependency = struct
  type func = Live.t -> Live.t
  type t = {mutable adj : (se * func) list; mutable rev_adj : (se * func) list}

  let createEmpty () = {adj = []; rev_adj = []}
end

let graph : (se, ValueDependency.t) Hashtbl.t = Hashtbl.create 10

let getDeps se =
  match Hashtbl.find_opt graph se with
  | Some deps -> deps
  | None ->
    let deps = ValueDependency.createEmpty () in
    Hashtbl.add graph se deps;
    deps

let print_graph () =
  prerr_endline "============= Graph =============";
  graph
  |> Hashtbl.iter (fun se1 (vd : ValueDependency.t) ->
         vd.adj
         |> List.iter (fun (se2, fn) ->
                PrintSE.print_se se1;
                prerr_string " --> ";
                PrintSE.print_se se2;
                prerr_newline ();
                PrintSE.print_live (fn Live.Top);
                prerr_newline ()))

let addEdge v1 v2 f =
  (* prerr_endline "@@@@@@@@@@@@ addEdge @@@@@@@@@@@"; *)
  (*   PrintSE.print_se v1; *)
  (*   prerr_newline (); *)
  (*   PrintSE.print_se v2; *)
  (* prerr_endline "================================"; *)
  let d1 = getDeps v1 in
  let d2 = getDeps v2 in
  d1.adj <- (v2, f) :: d1.adj;
  d2.rev_adj <- (v1, f) :: d2.rev_adj

let getLive se =
  Hashtbl.find_opt Live.liveness se |> Option.value ~default:Live.Bot

let hasSideEffect label =
  lookup_sc (Var (SideEff label)) |> SESet.mem SideEffect

let joinLive se live =
  match Hashtbl.find_opt Live.liveness se with
  | None -> Hashtbl.add Live.liveness se live
  | Some l -> Hashtbl.replace Live.liveness se (Live.join l live)

let meetLive se live =
  match Hashtbl.find_opt Live.liveness se with
  | None -> Hashtbl.add Live.liveness se live
  | Some l -> Hashtbl.replace Live.liveness se (Live.meet l live)

module ValueDependencyAnalysis = struct
  let ( >> ) f g x = g (f x)

  module Func = struct
    let top : Live.t -> Live.t = fun _ -> Live.Top

    let ifnotbot l : Live.t -> Live.t =
     fun x -> if Live.equal x Live.Bot then Live.Bot else l

    let iftop l : Live.t -> Live.t =
     fun x -> if Live.equal x Live.Top then l else Live.Bot

    let id : Live.t -> Live.t = fun x -> x
    let func : Live.t -> Live.t = fun body -> Func body

    let body : Live.t -> Live.t = function
      | Top -> Top
      | Bot -> Bot
      | Func b -> b
      | Ctor _ -> Bot

    let field ((ctor, i) : fld) : Live.t -> Live.t = function
      | Top -> Top
      | Bot -> Bot
      | Func _ -> Bot
      | Ctor cs -> (
        match cs |> CtorMap.find_opt ctor with
        | None -> Bot
        | Some ls ->
          List.nth_opt ls (i |> Option.value ~default:0)
          |> Option.value ~default:Live.Bot)

    let member name : Live.t -> Live.t = field (Member name, Some 0)

    let from_field ((ctor, i) : fld) : Live.t -> Live.t =
     fun l ->
      let ls =
        List.init
          (Option.value i ~default:0 + 1)
          (fun idx -> if Some idx = i then l else Bot)
      in
      Ctor (CtorMap.singleton ctor ls)

    let filter_field fld : Live.t -> Live.t = field fld >> from_field fld

    let ctor ctor : Live.t list -> Live.t =
     fun ls -> Ctor (CtorMap.singleton ctor ls)
  end

  let expr e = Var (Val (Label.of_expression e))
  let module_expr me = Var (Val (Label.of_module_expr me))

  let rec collectPath se (path : CL.Path.t) f =
    match path with
    | Pident id -> addEdge se (Id (Id.create !Current.cmtModName id)) f
    | Pdot (p', fld, _) ->
      collectPath se p' (f >> fun l -> Func.ctor (Member fld) [l])
    | Papply _ -> failwith "I don't know what Papply do"

  let rec collectBind cmtModName pat se (f : Live.t -> Live.t) =
    let collectBind = collectBind cmtModName in
    match pat.pat_desc with
    | Tpat_var (id, _) -> addEdge (Id (Id.create cmtModName id)) se f
    | Tpat_alias (pat, id, _) ->
      addEdge (Id (Id.create cmtModName id)) se f;
      collectBind pat se f
    | Tpat_tuple pats ->
      pats
      |> List.iteri (fun i pat ->
             collectBind pat se (Func.from_field (Tuple, Some i) >> f))
    | Tpat_construct (_, cstr_desc, pats) ->
      pats
      |> List.iteri (fun i pat ->
             collectBind pat se
               (Func.from_field (Construct cstr_desc.cstr_name, Some i) >> f))
    | Tpat_variant (_, None, _) -> ()
    | Tpat_variant (lbl, Some pat, _) ->
      collectBind pat se (Func.from_field (Variant lbl, Some 0) >> f)
    | Tpat_record (fields, _) ->
      fields
      |> List.iter (fun (_, label_desc, pat) ->
             collectBind pat se
               (Func.from_field (Record, Some label_desc.lbl_pos) >> f))
    | Tpat_array pats ->
      pats |> List.iter (fun pat -> collectBind pat se (Func.ifnotbot Live.Top))
    | Tpat_or (pat1, pat2, _) ->
      collectBind pat1 se f;
      collectBind pat2 se f
    | Tpat_lazy pat -> collectBind pat se (Func.ifnotbot Live.Top)
    | Tpat_any -> ()
    | Tpat_constant _ -> ()

  let analyze_prim_dep : CL.Primitive.description * Label.t list -> unit =
    function
    | {prim_name = "%ignore"}, [_] -> ()
    | _prim, args ->
      args |> List.iter (fun arg -> addEdge Top (Var (Val arg)) Func.top)

  let collectExpr e =
    match e.exp_desc with
    | Texp_ident (path, _, _) -> collectPath (expr e) path Func.id
    | Texp_constant _ -> ()
    | Texp_let (_, _, e_body) -> addEdge (expr e) (expr e_body) Func.id
    | Texp_function {cases} ->
      lookup_sc (expr e)
      |> SESet.iter (function
           | Fn (param, bodies) ->
             cases
             |> List.iter (fun case ->
                    collectBind !Current.cmtModName case.c_lhs (Var (Val param))
                      Func.id);
             bodies
             |> List.iter (fun body ->
                    addEdge (expr e) (Var (Val body)) Func.body);
             lookup_sc (Var (Val param))
             |> SESet.iter (function
                  | Var (Val arg) ->
                    addEdge (Var (Val param)) (Var (Val arg)) Func.id
                  | _ -> ())
           | _ -> ())
    | Texp_apply (e_f, args) ->
      lookup_sc (expr e)
      |> SESet.iter (function
           | PrimApp (prim, Some arg :: tl)
             when front_arg_len tl + 1 >= prim.prim_arity ->
             let prim_args, _tl' =
               Some arg :: tl |> ClosureAnalysis.split_arg prim.prim_arity
             in
             let _, seff = PrimResolution.value_prim (prim, prim_args) in
             if seff |> SESet.mem SideEffect then
               addEdge Top (expr e_f) Func.top;
             analyze_prim_dep (prim, prim_args)
           | _ -> ());
      let fn l =
        args
        |> List.fold_left
             (fun acc arg ->
               match snd arg with Some _ -> acc | None -> Func.body acc)
             l
        |> List.fold_right
             (fun arg acc ->
               match snd arg with Some _ -> Live.Func acc | None -> acc)
             args
      in
      addEdge (expr e) (expr e_f) fn
    | Texp_match (exp, cases, exn_cases, _) ->
      cases @ exn_cases
      |> List.iter (fun case ->
             addEdge (expr e) (expr case.c_rhs) Func.id;
             match case.c_guard with
             | Some guard ->
               addEdge (expr e) (expr guard) (Func.ifnotbot Live.Top)
             | None -> ());
      let cond_base =
        cases
        |> List.map (fun case -> Live.controlledByPat case.c_lhs)
        |> List.fold_left Live.join Live.Bot
      in
      cases
      |> List.iter (fun case ->
             collectBind !Current.cmtModName case.c_lhs (expr exp) Func.id);
      addEdge (expr e) (expr exp) (Func.ifnotbot cond_base);
      let casesHasSideEffect =
        List.fold_right
          (fun case acc ->
            let acc =
              acc || case.c_rhs |> Label.of_expression |> hasSideEffect
            in
            (match (acc, case.c_guard) with
            | true, Some exp_guard -> addEdge Top (expr exp_guard) Func.top
            | _ -> ());
            acc)
          cases false
      in
      let _ =
        List.fold_right
          (fun case acc ->
            let acc =
              acc || case.c_rhs |> Label.of_expression |> hasSideEffect
            in
            (match (acc, case.c_guard) with
            | true, Some exp_guard -> addEdge Top (expr exp_guard) Func.top
            | _ -> ());
            acc)
          exn_cases false
      in
      if casesHasSideEffect then
        let cond =
          cases
          |> List.fold_left
               (fun acc case -> Live.join acc (Live.controlledByPat case.c_lhs))
               Live.Bot
        in
        addEdge Top (expr exp) (fun _ -> cond)
    | Texp_try (exp, cases) ->
      addEdge (expr e) (expr exp) Func.id;
      cases
      |> List.iter (fun case ->
             addEdge (expr e) (expr case.c_rhs) Func.id;
             match case.c_guard with
             | Some guard ->
               addEdge (expr e) (expr guard) (Func.ifnotbot Live.Top)
             | None -> ())
    | Texp_tuple exps ->
      exps
      |> List.iteri (fun i exp ->
             addEdge (expr e) (expr exp) (Func.field (Tuple, Some i)))
    | Texp_construct (_, cstr_desc, exps) ->
      exps
      |> List.iteri (fun i exp ->
             addEdge (expr e) (expr exp)
               (Func.field (Construct cstr_desc.cstr_name, Some i)))
    | Texp_variant (_, None) -> ()
    | Texp_variant (label, Some exp) ->
      addEdge (expr e) (expr exp) (Func.field (Variant label, Some 0))
    | Texp_record {fields; extended_expression} -> (
      lookup_sc (expr e)
      |> SESet.iter (function
           | Ctor (Record, mems) ->
             List.combine mems (fields |> Array.to_list)
             |> List.iter (fun (mem, (ld, ldef)) ->
                    addEdge (expr e) (Mem mem)
                      (Func.field (Record, Some ld.lbl_pos));
                    match ldef with
                    | Kept _ -> ()
                    | Overridden (_, fe) -> addEdge (Mem mem) (expr fe) Func.id)
           | _ -> ());
      let fn live =
        let fields_live =
          fields
          |> Array.map (fun (ld, ldef) ->
                 match ldef with
                 | Overridden _ -> Live.Bot
                 | Kept _ -> live |> Func.field (Record, Some ld.lbl_pos))
          |> Array.to_list
        in
        Live.Ctor (CtorMap.singleton Record fields_live)
      in
      match extended_expression with
      | Some ee -> addEdge (expr e) (expr ee) fn
      | None -> ())
    | Texp_field (exp, _, ld) ->
      addEdge (expr e) (expr exp) (Func.from_field (Record, Some ld.lbl_pos))
    | Texp_setfield (exp1, _, ld, exp2) ->
      lookup_sc (expr exp1)
      |> SESet.iter (function
           | Ctor (Record, mems) -> (
             try addEdge (Mem (List.nth mems ld.lbl_pos)) (expr exp2) Func.id
             with _ -> ())
           | Unknown -> addEdge Top (expr exp2) Func.top
           | _ -> ());
      addEdge Top (expr exp1) (fun _ -> Live.empty_ctor)
    | Texp_array exps ->
      exps
      |> List.iter (fun exp ->
             addEdge (expr e) (expr exp) (Func.ifnotbot Live.Top))
    | Texp_ifthenelse (exp1, exp2, Some exp3) ->
      addEdge (expr e) (expr exp1) (Func.ifnotbot Live.Top);
      addEdge (expr e) (expr exp2) Func.id;
      addEdge (expr e) (expr exp3) Func.id;
      if
        exp2 |> Label.of_expression |> hasSideEffect
        || exp3 |> Label.of_expression |> hasSideEffect
      then addEdge Top (expr exp1) Func.top
    | Texp_ifthenelse (exp1, exp2, None) ->
      if exp2 |> Label.of_expression |> hasSideEffect then
        addEdge Top (expr exp1) Func.top
    | Texp_sequence (_, exp2) -> addEdge (expr e) (expr exp2) Func.id
    | Texp_while (exp1, exp2) ->
      if exp2 |> Label.of_expression |> hasSideEffect then
        addEdge Top (expr exp1) Func.top
    | Texp_for (id, _, exp1, exp2, _, exp3) ->
      addEdge (Id (Id.create !Current.cmtModName id)) (expr exp1) Func.id;
      addEdge (Id (Id.create !Current.cmtModName id)) (expr exp2) Func.id;
      if exp3 |> Label.of_expression |> hasSideEffect then
        addEdge Top (Id (Id.create !Current.cmtModName id)) Func.top
    | Texp_send (exp1, _, Some exp2) ->
      addEdge Top (expr exp1) Func.top;
      addEdge Top (expr exp2) Func.top
      (* addEdge (expr e) (expr exp1) (Func.ifnotbot Live.Top); *)
      (* addEdge (expr e) (expr exp2) (Func.ifnotbot Live.Top) *)
    | Texp_send (exp1, _, None) -> addEdge Top (expr exp1) Func.top
    (* addEdge (expr e) (expr exp1) (Func.ifnotbot Live.Top) *)
    | Texp_letmodule (x, _, me, exp) ->
      addEdge (Id (Id.create !Current.cmtModName x)) (module_expr me) Func.id;
      addEdge (expr e) (expr exp) Func.id
    | _ -> ()

  let rec pattern_fold_id_right f (pat : pattern) acc =
    let recurse = pattern_fold_id_right f in
    match pat.pat_desc with
    | Tpat_any | Tpat_constant _ -> acc
    | Tpat_var (x, _) -> acc |> f x
    | Tpat_alias (p, x, _) -> acc |> f x |> recurse p
    | Tpat_tuple pats -> acc |> List.fold_right recurse pats
    | Tpat_construct (_, _, pats) -> acc |> List.fold_right recurse pats
    | Tpat_variant (_, None, _) -> acc
    | Tpat_variant (_, Some p, _) -> acc |> recurse p
    | Tpat_record (fields, _) ->
      acc |> List.fold_right (fun (_, _, pat) -> recurse pat) fields
    | Tpat_array pats -> acc |> List.fold_right recurse pats
    | Tpat_lazy p -> acc |> recurse p
    | Tpat_or (lhs, rhs, _) -> acc |> recurse rhs |> recurse lhs

  let iter_id_in_pat f pat = pattern_fold_id_right (fun p () -> f p) pat ()

  let bindings_of_pat (pat : pattern) =
    pattern_fold_id_right List.cons pat []

  let collectStructItem se str_item members =
    let processMember id members =
      let name = id |> CL.Ident.name in
      if members |> StringSet.mem name then
        addEdge se (Id (Id.create !Current.cmtModName id)) (Func.member name);
      members |> StringSet.remove name
    in
    match str_item.str_desc with
    | Tstr_eval _ -> members
    | Tstr_value (_, vbs) ->
      let bindings = vbs |> List.map (fun vb -> bindings_of_pat vb.vb_pat) |> List.flatten in
      List.fold_right (processMember) bindings members
    | Tstr_module mb -> processMember mb.mb_id members
    | Tstr_recmodule mbs -> members |> List.fold_right (fun mb -> processMember mb.mb_id) mbs
    | Tstr_include {incl_mod; incl_type} ->
      let get_member_opt = function
        | Sig_value (x, _) | Sig_module (x, _, _) -> Some (CL.Ident.name x)
        | _ -> None
      in
      let exported = incl_type |> List.filter_map get_member_opt |> List.filter (fun name -> members |> StringSet.mem name) in
      let fn = fun x -> List.fold_right (fun name -> Live.join (Func.member name x)) exported Live.Bot in
      addEdge se (module_expr incl_mod) fn;
      StringSet.diff members (StringSet.of_list exported)
    | Tstr_primitive vd -> processMember vd.val_id members
    | _ -> members

  let collectStruct se str =
      let get_member_opt = function
        | Sig_value (x, _) | Sig_module (x, _, _) -> Some (CL.Ident.name x)
        | _ -> None
      in
    let members = str.str_type |> List.filter_map get_member_opt |> StringSet.of_list in
    List.fold_right (collectStructItem se) str.str_items members

  let collectModuleExpr (me : module_expr) =
    match me.mod_desc with
    | Tmod_ident (path, _) -> collectPath (module_expr me) path Func.id
    | Tmod_structure str -> collectStruct (module_expr me) str |> ignore
    | Tmod_functor (x, _, _, _) ->
      lookup_sc (module_expr me)
      |> SESet.iter (function
           | Fn (param, _) ->
             addEdge
               (Id (Id.create !Current.cmtModName x))
               (Var (Val param)) Func.id;
             lookup_sc (Var (Val param))
             |> SESet.iter (function
                  | Var (Val arg) ->
                    addEdge (Var (Val param)) (Var (Val arg)) Func.id
                  | _ -> ())
           | _ -> ())
    | Tmod_apply (me_f, _, _) ->
      lookup_sc (module_expr me)
      |> SESet.iter (function
           | App (f, Some _ :: tl) -> (
             addEdge (module_expr me) (Var (Val f)) (Func.ifnotbot Live.Top);
             match tl with
             | [] ->
               lookup_sc (Var (Val f))
               |> SESet.iter (function
                    | Fn (_, bodies) ->
                      bodies
                      |> List.iter (fun body ->
                             addEdge (module_expr me) (Var (Val body)) Func.id)
                    | _ -> ())
             | _ -> ())
           | _ -> ());
      addEdge (module_expr me) (module_expr me_f) (Func.ifnotbot Live.Top)
    | Tmod_constraint (mexp, _, _, _) ->
      addEdge (module_expr me) (module_expr mexp) Func.id
    | Tmod_unpack (e, _) -> addEdge (module_expr me) (expr e) Func.id

  let collectMapper =
    let super = CL.Tast_mapper.default in
    let value_binding self vb =
      collectBind !Current.cmtModName vb.vb_pat (expr vb.vb_expr) Func.id;
      if vb.vb_attributes |> annotatedAsLive then
        vb.vb_pat
        |> iter_id_in_pat (fun id ->
               addEdge Top (Id (Id.create !Current.cmtModName id)) Func.top);
      super.value_binding self vb
    in
    let module_binding self mb =
      addEdge
        (Id (Id.create !Current.cmtModName mb.mb_id))
        (module_expr mb.mb_expr) Func.id;
      super.module_binding self mb
    in
    let expr self e =
      collectExpr e;
      super.expr self e
    in
    let module_expr self me =
      collectModuleExpr me;
      super.module_expr self me
    in
    {super with expr; module_expr; value_binding; module_binding}

  let scc () : se list list =
    let counter = ref 0 in
    let stack = Stack.create () in
    let num = Hashtbl.create 256 in
    let getnum vm =
      match Hashtbl.find_opt num vm with Some res -> res | None -> 0
    in
    let finished = ref SESet.empty in
    let markfinished vm = finished := !finished |> SESet.add vm in
    let isfinished vm = !finished |> SESet.mem vm in
    let scc = Stack.create () in
    let rec dfs v =
      counter := !counter + 1;
      Hashtbl.add num v !counter;
      stack |> Stack.push v;
      let result =
        (getDeps v).adj
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
          if compare_se t v = 0 then break := true
        done;
        scc |> Stack.push (nodes |> Stack.to_seq |> List.of_seq));
      result
    in
    graph |> Hashtbl.to_seq_keys
    |> Seq.iter (fun node -> if getnum node = 0 then dfs node |> ignore);
    scc |> Stack.to_seq |> List.of_seq

  let collect cmtMod =
    Current.cmtModName := cmtMod.modname;
    addEdge
      (Id (Id.createCmtModuleId cmtMod.modname))
      (Var (Val cmtMod.label)) Func.id;
    collectStruct (Var (Val cmtMod.label)) cmtMod.structure |> ignore;
    collectMapper.structure collectMapper cmtMod.structure |> ignore;
    ()

  let solve () =
    lookup_sc AppliedToUnknown
    |> SESet.iter (function
         | Var (Val label) -> addEdge Top (Var (Val label)) Func.top
         | _ -> ());
    let dag = scc () in
    let dependentsLives node =
      let dependents = (getDeps node).rev_adj in
      dependents
      |> List.fold_left
           (fun acc (dep, f) -> dep |> Live.get |> f |> Live.join acc)
           Live.Bot
    in
    (* prerr_endline "============ SCC Order ============="; *)
    dag
    |> List.iter (fun nodes ->
           (* prerr_int (nodes |> List.length); *)
           (* prerr_newline (); *)
           (* nodes |> List.iter (fun node -> PrintSE.print_se node; prerr_newline ()); *)
           match nodes with
           | [] -> raise (RuntimeError "Empty SCC")
           | [node] ->
             (* Value.print node; *)
             joinLive node (dependentsLives node)
           | _ ->
             nodes |> List.iter (fun node -> joinLive node Live.Top);
             for i = 1 to 5 do
               nodes
               |> List.iter (fun node -> meetLive node (dependentsLives node))
             done)
end

let traverse_ast =
  let super = CL.Tast_mapper.default in
  let expr self (expr : expression) =
    let v, seff = se_of_expr expr in
    init_sc (Var (Val (Label.of_expression expr))) v;
    init_sc (Var (SideEff (Label.of_expression expr))) seff;
    super.expr self expr
  in
  let module_expr self (me : module_expr) =
    let v, seff = se_of_module_expr me in
    init_sc (Var (Val (Label.of_module_expr me))) v;
    init_sc (Var (SideEff (Label.of_module_expr me))) seff;
    super.module_expr self me
  in
  {super with expr; module_expr}

let preprocess =
  let super = CL.Tast_mapper.default in
  let expr self e =
    let e' = Label.preprocess_expression e in
    super.expr self e'
  in
  let module_expr self me =
    let me' = Label.preprocess_module_expr me in
    super.module_expr self me'
  in
  {super with expr; module_expr}

let cmtStructures : cmt_structure list ref = ref []

let processCmtStructure modname (structure : CL.Typedtree.structure) =
  print_endline "processCmtStructure";
  print_endline modname;
  Print.print_structure structure;
  print_newline ();
  let structure = structure |> preprocess.structure preprocess in
  structure |> traverse_ast.structure traverse_ast |> ignore;
  let label = Label.new_cmt_module modname in
  let v, seff = se_of_struct structure in
  init_sc (Id (Id.createCmtModuleId modname)) [Var (Val label)];
  init_sc (Var (Val label)) v;
  init_sc (Var (SideEff label)) seff;
  cmtStructures := {structure; label; modname} :: !cmtStructures

let processCmt (cmt_infos : CL.Cmt_format.cmt_infos) =
  Current.cmtModName := cmt_infos.cmt_modname;
  (* let moduleId = Id.createCmtModuleId !Current.cmtModName in *)
  match cmt_infos.cmt_annots with
  | Interface _ -> ()
  | Implementation structure ->
    processCmtStructure cmt_infos.cmt_modname structure
  | _ -> ()

let isDeadValue se = se |> Live.get = Live.Bot

let isDeadExpr label =
  Var (Val label) |> isDeadValue && not (label |> hasSideEffect)

let rec collectDeadPattern addDeadValue pat =
  let recurse = collectDeadPattern addDeadValue in
  match pat.pat_desc with
  | Tpat_any -> ()
  | Tpat_var (id, _) ->
    let se = Id (Id.create !Current.cmtModName id) in
    if se |> isDeadValue then addDeadValue se
  | Tpat_alias (p, id, _) ->
    let se = Id (Id.create !Current.cmtModName id) in
    if se |> isDeadValue then addDeadValue se;
    recurse p
  | Tpat_constant _ -> ()
  | Tpat_tuple pats -> pats |> List.iter recurse
  | Tpat_construct (_, _, pats) -> pats |> List.iter recurse
  | Tpat_variant (_, None, _) -> ()
  | Tpat_variant (_, Some pat, _) -> recurse pat
  | Tpat_record (fields, _) ->
    fields |> List.iter (fun (_, _, pat) -> recurse pat)
  | Tpat_array pats -> pats |> List.iter recurse
  | Tpat_or (pat1, pat2, _) ->
    recurse pat1;
    recurse pat2
  | Tpat_lazy pat -> recurse pat

let collectDeadValuesMapper addDeadValue =
  let addDeadExpr label = addDeadValue (Var (Val label)) in
  let super = CL.Tast_mapper.default in
  let pat self p =
    collectDeadPattern addDeadValue p;
    super.pat self p
  in
  let expr self e =
    let label = Label.of_expression e in
    if label |> isDeadExpr then (
      (match label |> Label.to_summary with
      | ValueExpr e -> if not (e.exp_type |> isUnitType) then addDeadExpr label
      | _ -> addDeadExpr label);
      e)
    else super.expr self e
  in
  let module_expr self me =
    let label = me |> Label.of_module_expr in
    if label |> isDeadExpr then (
      addDeadExpr label;
      me)
    else super.module_expr self me
  in

  {super with expr; module_expr; pat}

let collectDeadValues cmts =
  let deads = ref SESet.empty in
  let addDeadValue se = deads := !deads |> SESet.add se in
  let addDeadExpr label = addDeadValue (Var (Val label)) in
  let mapper = collectDeadValuesMapper addDeadValue in
  cmts
  |> List.iter (fun {structure; label; modname} ->
         if isDeadExpr label then addDeadExpr label
         else (
           Current.cmtModName := modname;
           mapper.structure mapper structure |> ignore));
  (* ValueAnalysis.tbl *)
  (* |> Hashtbl.iter (fun vm _ -> *)
  (*        match vm with *)
  (*        | V_Name name -> *)
  (*          if (ValueAnalysis.get vm).liveness = Live.Bot then *)
  (*            deads := !deads |> ValueSet.add vm *)
  (*        | _ -> ()); *)
  !deads

let reportDead ~ppf =
  solve ();
  !cmtStructures |> List.iter ValueDependencyAnalysis.collect;
  ValueDependencyAnalysis.solve ();
  PrintSE.print_sc_info ();
  prerr_endline "============ Dead Values =============";
  let deads = collectDeadValues !cmtStructures in
  deads
  |> SESet.iter (fun se ->
         PrintSE.print_se se;
         (match se with
         | Var (Val label) -> (
           match label |> Label.to_summary with
           | ValueExpr e ->
             (* Print.print_expression 0 e.exp; *)
             (* prerr_newline (); *)
             ()
           | ModExpr me ->
             (* Print.print_module_expr me.mod_exp; *)
             (* prerr_newline (); *)
             ()
           | _ -> ())
         | _ -> ());
         prerr_newline ());
  (* print_graph (); *)
  (* PrintSE.print_sc_info (); *)
  (* !cmtStructures |> List.iter (fun cmt_str -> *)
  (*   Print.print_structure cmt_str.structure; *)
  (* ); *)
  ()
