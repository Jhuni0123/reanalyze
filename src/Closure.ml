open CL.Typedtree
open CL.Types
open DVACommon

exception RuntimeError of string

module StringMap = Map.Make (String)

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
  type item = (se * se)
  type t = item Queue.t

  let push : item -> t -> unit = Queue.push
  let pop : t -> item = Queue.pop
  let is_empty : t -> bool = Queue.is_empty
  let create : unit -> t = Queue.create
end

let worklist : Worklist.t = Worklist.create ()

let sc : SESet.t SETbl.t = (
  let tbl = SETbl.create 256 in
  let _ = SETbl.add tbl UsedInUnknown SESet.empty in
  tbl
)
let reverse_sc : WorkItemSet.t SETbl.t = SETbl.create 256

let lookup_sc se =
  try SETbl.find sc se with Not_found -> SESet.singleton Unknown

let propagate = function
  | Unknown | Ctor _ | Prim _ | Fn _ | FnApp (_, _, None :: _) -> true
  | PrimApp (prim, args) -> front_arg_len args < prim.prim_arity
  | SideEffect -> true
  | _ -> false

let add_reverse se workitem =
  match SETbl.find_opt reverse_sc se with
  | None -> SETbl.add reverse_sc se (WorkItemSet.singleton workitem)
  | Some orig -> SETbl.replace reverse_sc se (WorkItemSet.add workitem orig)

let update_reverse (key, elt) =
  match key with
  | Mem _ | Id _ | Var _ -> (
    add_reverse elt (WorkPair (key, elt));
    match (key, elt) with
    | Var _, Fld (e, _) | Var _, App (e, Some _ :: _) ->
      add_reverse (Var (Val e)) (WorkPair (key, elt))
    | _ -> ())
  | Fld (e, _) -> add_reverse (Var (Val e)) (WorkPair (key, elt))
  | UsedInUnknown -> add_reverse elt (WorkPair (key, elt))
  | _ -> failwith "Invalid LHS"

let get_workitems (key, elt) =
  let items = WorkItemSet.singleton (WorkPair (key, elt)) in
  match key with
  | Mem _ | Id _ | Var _ when propagate elt -> (
    match SETbl.find_opt reverse_sc key with
    | Some rev -> WorkItemSet.union rev items
    | None -> items)
  | _ -> items

let init_sc lhs data =
  data |> List.iter (fun rhs -> worklist |> Worklist.push (lhs, rhs));
  let set = SESet.of_list data in
  match SETbl.find sc lhs with
  | exception Not_found -> SETbl.add sc lhs set
  | original -> SETbl.replace sc lhs (SESet.union original set)

let update_sc lhs added =
  let original = lookup_sc lhs in
  let diff = SESet.diff added original in
  if not (SESet.is_empty diff) then (
    diff |> SESet.iter (fun rhs -> worklist |> Worklist.push (lhs, rhs));
    SETbl.replace sc lhs (SESet.union original diff))

module PrimResolution = struct
  let allocated = Hashtbl.create 10

  let value_prim : (CL.Primitive.description * Label.t list) -> SESet.t * SESet.t = function
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
        let i = Label.new_memory (Label.ctx x) in
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
    | _prim, args ->
        update_sc UsedInUnknown (args |> List.map (fun arg -> Var (Val arg)) |> SESet.of_list);
        (SESet.singleton Unknown, SESet.singleton SideEffect)
end

let list_split_flatten l =
  let a, b = List.split l in
  (List.flatten a, List.flatten b)

let rec split_arg n args =
  match n with
  | 0 -> ([], args)
  | _ -> (
    match args with
    | Some hd :: tl ->
      let hds, rem = split_arg (n - 1) tl in
      (hd :: hds, rem)
    | _ -> raise (RuntimeError "Invalid args"))

let rec merge_args = function
  | [], l -> l
  | l, [] -> l
  | None :: tl, hd :: l -> hd :: merge_args (tl, l)
  | Some x :: tl, l -> Some x :: merge_args (tl, l)

let rec label_of_path path =
  match path with
  | CL.Path.Papply (_f, _x) ->
    raise (RuntimeError "I don't know what Papply do.")
    (* let f = label_of_path f in *)
    (* let x = label_of_path x in *)
    (* let temp = Label.new_temp () in *)
    (* init_sc (Var (Val temp)) [App (f, [Some x])]; *)
    (* temp *)
  | CL.Path.Pdot (x, fld, _) ->
    let x = label_of_path x in
    let label = Label.new_path path in
    init_sc (Var (Val label)) [Fld (x, (Member fld, Some 0))];
    label
  | CL.Path.Pident x ->
    let label = Label.new_path path in
    init_sc (Var (Val label)) [Id (Id.create x)];
    label

let rec solve_pat (pat : pattern) (e : Label.t) =
  (* Does not return its set expression, as it does not require screening *)
  match pat.pat_desc with
  | Tpat_any | Tpat_constant _ -> []
  | Tpat_var (x, _) ->
    update_sc (Id (Id.create x)) (SESet.singleton (Var (Val e)));
    [(x, e)]
  | Tpat_alias (p, x, _) ->
    update_sc (Id (Id.create x)) (SESet.singleton (Var (Val e)));
    solve_pat p e @ [(x, e)]
  | Tpat_tuple pats ->
    pats
    |> List.mapi (fun idx pat ->
           let temp = Label.new_temp () in
           init_sc (Var (Val temp)) [Fld (e, (Tuple, Some idx))];
           solve_pat pat temp)
    |> List.flatten
  | Tpat_construct (_, cstr_desc, pats) ->
    pats
    |> List.mapi (fun idx pat ->
           let temp = Label.new_temp () in
           init_sc (Var (Val temp))
             [Fld (e, (Construct cstr_desc.cstr_name, Some idx))];
           solve_pat pat temp)
    |> List.flatten
  | Tpat_variant (lbl, p_o, _) -> (
    let constructor = Variant lbl in
    match p_o with
    | None -> []
    | Some p ->
      let temp = Label.new_temp () in
      init_sc (Var (Val temp)) [Fld (e, (constructor, Some 0))];
      solve_pat p temp)
  | Tpat_record (fields, _) ->
    fields
    |> List.map (fun (_, lbl, pat) ->
           let temp = Label.new_temp () in
           init_sc (Var (Val temp)) [Fld (e, (Record, Some lbl.lbl_pos))];
           solve_pat pat temp)
    |> List.flatten
  | Tpat_array pats ->
    pats
    |> List.mapi (fun idx pat ->
           let temp = Label.new_temp () in
           init_sc (Var (Val temp)) [Fld (e, (Array, Some idx))];
           solve_pat pat temp)
    |> List.flatten
  | Tpat_lazy p ->
    solve_pat p e
    (* let temp = new_temp_var () in *)
    (* init_sc (Var temp) [App_v (e, [])]; *)
    (* solve_eq p temp update_tbl *)
  | Tpat_or (lhs, rhs, _) -> solve_pat lhs e @ solve_pat rhs e

let rec _evaluate_expresion expr =
  let solve_param (expr : Label.t) pattern : unit =
    solve_pat pattern expr |> ignore
  in
  match expr.exp_desc with
  | Texp_ident (_, _, {val_kind = Val_prim prim}) -> (
    match prim.prim_arity with 0 -> ([Unknown], []) | _ -> ([Prim prim], []))
  | Texp_ident (x, _, _) -> ([Var (Val (label_of_path x))], [])
  | Texp_constant _ -> ([], [])
  | Texp_let (_, vbs, e) ->
    let _, seff = vbs |> List.map evaluate_value_binding |> list_split_flatten in
    evaluate_expression e;
    ( [Var (Val (Label.of_expression e))],
      Var (SideEff (Label.of_expression e)) :: seff )
  | Texp_function {param; cases} ->
    let pats = cases |> List.map (fun case -> case.c_lhs) in
    let bodies = cases |> List.map (fun case -> case.c_rhs) in
    let param_label = Label.new_param param in
    init_sc (Var (Val param_label)) [];
    pats |> List.iter (solve_param param_label);
    ([Fn (param_label, bodies |> List.map Label.of_expression)], [])
  | Texp_apply (e, args) ->
    evaluate_expression e;
    args |> List.iter (function
      | (_, Some ae) -> evaluate_expression ae
      | _ -> ()
    );
    let arg_labels =
      args |> List.map (fun (_, aeo) -> Option.map Label.of_expression aeo)
    in
    let seff =
      args
      |> List.fold_left
           (fun acc (_, exp_o) ->
             match exp_o with
             | None -> acc
             | Some exp -> Var (SideEff (Label.of_expression exp)) :: acc)
           []
    in
    let v = [App (Label.of_expression e, arg_labels)] in
    let seff = Var (SideEff (Label.of_expression e)) :: seff in
    (v, seff)
  | Texp_match (exp, cases, exn_cases, _) ->
    evaluate_expression exp;
    cases @ exn_cases |> List.iter (fun case ->
      evaluate_expression case.c_rhs;
      match case.c_guard with
      | Some g -> evaluate_expression g
      | _ -> ()
    );
    let pats = cases |> List.map (fun case -> case.c_lhs) in
    let exp_label = Label.of_expression exp in
    let () = pats |> List.iter (solve_param exp_label) in
    let rhs_labels =
      cases @ exn_cases |> List.map (fun case -> Label.of_expression case.c_rhs)
    in
    let v = rhs_labels |> List.map (fun label -> Var (Val label)) in
    let seff = rhs_labels |> List.map (fun label -> Var (SideEff label)) in
    (v, Var (SideEff (Label.of_expression exp)) :: seff)
  | Texp_try (exp, cases) ->
    evaluate_expression exp;
    cases |> List.iter (fun case ->
      evaluate_expression case.c_rhs;
      match case.c_guard with
      | Some g -> evaluate_expression g
      | _ -> ()
    );
    let label = Label.of_expression exp in
    let ses =
      cases |> List.map (fun case -> Var (Val (Label.of_expression case.c_rhs)))
    in
    (Var (Val label) :: ses, [Var (SideEff label)])
  | Texp_tuple exps ->
    exps |> List.iter evaluate_expression;
    let v = [Ctor (Tuple, exps |> List.map Label.of_expression)] in
    let seff =
      exps |> List.map (fun e -> Var (SideEff (Label.of_expression e)))
    in
    (v, seff)
  | Texp_construct (_, _, []) -> ([], [])
  | Texp_construct (_, {cstr_name}, exps) ->
    exps |> List.iter evaluate_expression;
    let v =
      [Ctor (Construct cstr_name, exps |> List.map Label.of_expression)]
    in
    let seff =
      exps |> List.map (fun e -> Var (SideEff (Label.of_expression e)))
    in
    (v, seff)
  | Texp_variant (lbl, Some exp) ->
    evaluate_expression exp;
    let v = [Ctor (Variant lbl, [Label.of_expression exp])] in
    let seff = [Var (SideEff (Label.of_expression exp))] in
    (v, seff)
  | Texp_variant (_, None) -> ([], [])
  | Texp_record {fields; extended_expression} ->
    let for_each_field
        ((lbl_desc : label_description), (lbl_def : record_label_definition)) =
      let mem = Label.new_memory !Current.cmtModName in
      init_sc (Mem mem)
        (match lbl_def with
        | Kept _ -> (
          match extended_expression with
          | Some e ->
            [Fld (Label.of_expression e, (Record, Some lbl_desc.lbl_pos))]
          | None -> [])
        | Overridden (_, e) ->
            evaluate_expression e;
            [Var (Val (Label.of_expression e))]);
      mem
    in
    let v =
      [Ctor (Record, fields |> Array.map for_each_field |> Array.to_list)]
    in
    let seff =
      match extended_expression with
      | Some e -> evaluate_expression e; [Var (SideEff (Label.of_expression e))]
      | None -> []
    in
    let seff =
      fields
      |> Array.fold_left
           (fun acc (_, lbl_def) ->
             match lbl_def with
             | Kept _ -> acc
             | Overridden (_, e) -> Var (SideEff (Label.of_expression e)) :: acc)
           seff
    in
    (v, seff)
  | Texp_field (e, _, lbl) ->
    evaluate_expression e;
    let v = [Fld (Label.of_expression e, (Record, Some lbl.lbl_pos))] in
    let seff = [Var (SideEff (Label.of_expression e))] in
    (v, seff)
  | Texp_setfield (e1, _, lbl, e2) ->
    evaluate_expression e1;
    evaluate_expression e2;
    let val1 = Label.of_expression e1 in
    let val2 = Var (Val (Label.of_expression e2)) in
    init_sc (Fld (val1, (Record, Some lbl.lbl_pos))) [val2];
    ([], [SideEffect])
  | Texp_array exps ->
    exps |> List.iter evaluate_expression;
    let mem = Label.new_memory !Current.cmtModName in
    let elements = exps |> List.map (fun exp -> Var (Val (Label.of_expression exp))) in
    init_sc (Mem mem) elements;
    let v = [Ctor (Array, [mem])] in
    let seff =
      exps |> List.map (fun e -> Var (SideEff (Label.of_expression e)))
    in
    (v, seff)
  | Texp_ifthenelse (exp, exp_true, Some exp_false) ->
    evaluate_expression exp;
    evaluate_expression exp_true;
    evaluate_expression exp_false;
    let val1 = Var (Val (Label.of_expression exp_true)) in
    let val2 = Var (Val (Label.of_expression exp_false)) in
    let seff0 = Var (SideEff (Label.of_expression exp)) in
    let seff1 = Var (SideEff (Label.of_expression exp_true)) in
    let seff2 = Var (SideEff (Label.of_expression exp_false)) in
    ([val1; val2], [seff0; seff1; seff2])
  | Texp_ifthenelse (exp, exp_true, None) ->
    evaluate_expression exp;
    evaluate_expression exp_true;
    let seff0 = Var (SideEff (Label.of_expression exp)) in
    let seff1 = Var (SideEff (Label.of_expression exp_true)) in
    ([Var (Val (Label.of_expression exp_true))], [seff0; seff1])
  | Texp_sequence (exp1, exp2) ->
    evaluate_expression exp1;
    evaluate_expression exp2;
    let val2 = Var (Val (Label.of_expression exp2)) in
    let seff1 = Var (SideEff (Label.of_expression exp1)) in
    let seff2 = Var (SideEff (Label.of_expression exp2)) in
    ([val2], [seff1; seff2])
  | Texp_while (exp_cond, exp_body) ->
    evaluate_expression exp_cond;
    evaluate_expression exp_body;
    let seff_cond = Var (SideEff (Label.of_expression exp_cond)) in
    let seff_body = Var (SideEff (Label.of_expression exp_body)) in
    ([], [seff_cond; seff_body])
  | Texp_for (_, _, exp1, exp2, _, exp_body) ->
    evaluate_expression exp1;
    evaluate_expression exp2;
    evaluate_expression exp_body;
    let seff1 = Var (SideEff (Label.of_expression exp1)) in
    let seff2 = Var (SideEff (Label.of_expression exp2)) in
    let seff_body = Var (SideEff (Label.of_expression exp_body)) in
    ([], [seff1; seff2; seff_body])
  | Texp_letmodule (x, _, me, e) ->
    evaluate_module_expr me;
    evaluate_expression e;
    let val_m = Var (Val (Label.of_module_expr me)) in
    let val_e = Var (Val (Label.of_expression e)) in
    update_sc (Id (Id.create x)) (SESet.singleton val_m);
    let seff_m = Var (SideEff (Label.of_module_expr me)) in
    let seff_e = Var (SideEff (Label.of_expression e)) in
    ([val_e], [seff_m; seff_e])
  | Texp_pack me ->
    evaluate_module_expr me;
    ( [Var (Val (Label.of_module_expr me))],
      [Var (SideEff (Label.of_module_expr me))] )
  | Texp_send (e, _, None) ->
      evaluate_expression e;
      ([Unknown], [SideEffect])
  | Texp_send (e, _, Some e2) ->
      evaluate_expression e;
      evaluate_expression e2;
      ([Unknown], [SideEffect])
  | Texp_letexception (_, e) ->
    evaluate_expression e;
    let v = Var (Val (Label.of_expression e)) in
    let seff = Var (SideEff (Label.of_expression e)) in
    ([v], [seff])
  | Texp_lazy exp ->
    (* FIXME: handle lazy *)
    evaluate_expression exp;
    (* let temp = Label.new_temp () in *)
    (* ([Fn (temp, [Label.of_expression exp])], []) *)
    ( [Var (Val (Label.of_expression exp))],
      [Var (SideEff (Label.of_expression exp))] )
  | _ -> ([], [])

and evaluate_expression e =
  let evaluated =  lookup_sc (Var (SideEff (Label.of_expression e))) |> SESet.mem Evaluated in
  if not evaluated then (
    Current.cmtModName := fst (Label.of_expression e);
    let v, seff = _evaluate_expresion e in
    update_sc (Var (Val (Label.of_expression e))) (SESet.of_list v);
    update_sc (Var (SideEff (Label.of_expression e))) (SESet.of_list seff);
    update_sc (Var (SideEff (Label.of_expression e))) (SESet.singleton Evaluated);
  )

and _evaluate_module_expr (m : CL.Typedtree.module_expr) =
  match m.mod_desc with
  | Tmod_functor (x, _, _, me) ->
    let param = Label.new_param x in
    update_sc (Id (Id.create x)) (SESet.singleton (Var (Val param)));
    ([Fn (param, [Label.of_module_expr me])], [])
  | Tmod_ident (x, _) ->
    let x = label_of_path x in
    ([Var (Val x)], [])
  | Tmod_structure structure -> evaluate_struct structure
  | Tmod_apply (func, arg, _) ->
    evaluate_module_expr func;
    evaluate_module_expr arg;
    let v =
      [App (Label.of_module_expr func, [Some (Label.of_module_expr arg)])]
    in
    let seff_f = Var (SideEff (Label.of_module_expr func)) in
    let seff_arg = Var (SideEff (Label.of_module_expr arg)) in
    (v, [seff_f; seff_arg])
  | Tmod_constraint (m, _, _, _) ->
    evaluate_module_expr m;
    ( [Var (Val (Label.of_module_expr m))],
      [Var (SideEff (Label.of_module_expr m))] )
  | Tmod_unpack (e, _) ->
    evaluate_expression e;
    ( [Var (Val (Label.of_expression e))],
      [Var (SideEff (Label.of_expression e))] )

and evaluate_module_expr (me : CL.Typedtree.module_expr) =
  let evaluated =  lookup_sc (Var (SideEff (Label.of_module_expr me))) |> SESet.mem Evaluated in
  if not evaluated then (
    let v, seff = _evaluate_module_expr me in
    update_sc (Var (Val (Label.of_module_expr me))) (SESet.of_list v);
    update_sc (Var (SideEff (Label.of_module_expr me))) (SESet.of_list seff);
    update_sc (Var (SideEff (Label.of_module_expr me))) (SESet.singleton Evaluated);
  )

and evaluate_module_binding (mb : module_binding) =
  evaluate_module_expr mb.mb_expr;
  let label = Label.of_module_expr mb.mb_expr in
  update_sc (Id (Id.create mb.mb_id)) (SESet.singleton (Var (Val label)));
  ([(mb.mb_id, label)], [Var (SideEff label)])

and evaluate_value_binding (vb : value_binding) =
  evaluate_expression vb.vb_expr;
  if vb.vb_attributes |> annotatedAsLive then
    ids_in_pat vb.vb_pat |> List.iter (fun (x, _) -> update_sc UsedInUnknown (SESet.singleton (Id (Id.create x))));
  let bindings = solve_pat vb.vb_pat (Label.of_expression vb.vb_expr) in
  (* let v = bindings |> List.map (fun (name, e) -> Ctor (Member name, [e])) in *)
  let seff = Var (SideEff (Label.of_expression vb.vb_expr)) in
  (bindings, [seff])

and evaluate_struct_item (item : structure_item) =
  match item.str_desc with
  | Tstr_eval (e, _) ->
      evaluate_expression e;
      ([], [Var (SideEff (Label.of_expression e))])
  | Tstr_value (_, vbs) -> vbs |> List.map evaluate_value_binding |> list_split_flatten
  | Tstr_module mb -> evaluate_module_binding mb
  | Tstr_recmodule mbs -> mbs |> List.map evaluate_module_binding |> list_split_flatten
  | Tstr_include {incl_mod; incl_type} ->
    evaluate_module_expr incl_mod;
    let incl_label = Label.of_module_expr incl_mod in
    (* rebind included values & modules *)
    let for_each_sig_item :
        CL.Types.signature_item -> (CL.Ident.t * Label.t) option = function
      | Sig_value (x, _) | Sig_module (x, _, _) ->
        let temp = Label.new_temp () in
        let id = Id.create x in
        init_sc (Id id) [Var (Val temp)];
        init_sc (Var (Val temp))
          [Fld (incl_label, (Member (Id.name id), Some 0))];
        Some (x, temp)
      | _ -> None
    in
    (incl_type |> List.filter_map for_each_sig_item, [])
  | Tstr_primitive vd ->
    let temp = Label.new_temp () in
    init_sc (Var (Val temp)) [Unknown];
    update_sc (Id (Id.create vd.val_id)) (SESet.singleton (Var (Val temp)));
    (* ([Ctor (Member (CL.Ident.name vd.val_id), [temp])], []) *)
    ([(vd.val_id, temp)], [])
  | _ -> ([], [])

and evaluate_struct str =
  let bindings, seff =
    str.str_items |> List.map evaluate_struct_item |> list_split_flatten
  in
  let v =
    bindings
    |> List.map (fun (id, l) -> (CL.Ident.name id, l))
    |> List.to_seq |> StringMap.of_seq |> StringMap.bindings
    |> List.map (fun (name, label) -> Ctor (Member name, [label]))
  in
  (v, seff)

and evaluate_label l =
  match Label.to_summary l with
  | ValueExpr es -> evaluate_expression es.exp_labeled
  | ModExpr mes -> evaluate_module_expr mes.mod_exp_labeled
  | _ -> ()

let traverse_init_sc =
  let super = CL.Tast_mapper.default in
  let pat self p =
    (match p.pat_desc with
    | Tpat_var (x, _) -> init_sc (Id (Id.create x)) []
    | Tpat_alias (_, x, _) -> init_sc (Id (Id.create x)) []
    | _ -> ()
    );
    super.pat self p
  in
  let module_binding self mb =
    init_sc (Id (Id.create mb.mb_id)) [];
    super.module_binding self mb
  in
  let structure_item self item =
    (match item.str_desc with
    | Tstr_primitive vd -> init_sc (Id (Id.create vd.val_id)) []
    | _ -> ()
    );
    super.structure_item self item
  in
  let expr self (expr : expression) =
    (match expr.exp_desc with
    | Texp_for (x, _, _, _, _, _) -> init_sc (Id (Id.create x)) []
    | Texp_letmodule (x, _, _, _) -> init_sc (Id (Id.create x)) []
    | _ -> ());
    init_sc (Var (Val (Label.of_expression expr))) [];
    init_sc (Var (SideEff (Label.of_expression expr))) [];
    super.expr self expr
  in
  let module_expr self (me : module_expr) =
    (match me.mod_desc with
    | Tmod_functor (x, _, _, _) -> init_sc (Id (Id.create x)) [];
    | _ -> ()
    );
    init_sc (Var (Val (Label.of_module_expr me))) [];
    init_sc (Var (SideEff (Label.of_module_expr me))) [];
    super.module_expr self me
  in
  {super with pat; module_binding; structure_item; expr; module_expr}

let init_cmt_structure modname structure =
  let label = Label.new_cmt_module modname in
  let v, seff = evaluate_struct structure in
  init_sc (Id (Id.createCmtModuleId modname)) [Var (Val label)];
  init_sc (Var (Val label)) v;
  init_sc (Var (SideEff label)) seff;
  label

let reduce_app f args =
  match f with
  | Unknown ->
    args
    |> List.iter (fun arg ->
           match arg with
           | None -> ()
           | Some label ->
             update_sc UsedInUnknown (SESet.singleton (Var (Val label))));
    (SESet.singleton Unknown, SESet.singleton SideEffect)
  | Fn (param, bodies) ->
    (SESet.singleton (FnApp (param, bodies, args)), SESet.empty)
  | Prim p ->
    (SESet.singleton (PrimApp (p, args)), SESet.empty)
  | FnApp (param, bodies, (None :: _ as args')) ->
    (SESet.singleton (FnApp (param, bodies, merge_args (args', args))), SESet.empty)
  | PrimApp (p, args') when front_arg_len args' < p.prim_arity ->
    let args = merge_args (args', args) in
    (SESet.singleton (PrimApp (p, args)), SESet.empty)
  | _ -> (SESet.empty, SESet.empty)

let reduce_fld se fld =
  match se with
  | Unknown -> SESet.singleton Unknown
  | Ctor (kappa, l) -> (
    match fld with
    | kappa', Some i when kappa' = kappa && i < List.length l ->
      let ith =
        match kappa with
        | Record -> Mem (List.nth l i)
        | _ -> Var (Val (List.nth l i))
      in
      SESet.singleton ith
    | _ -> SESet.empty)
  | _ -> SESet.empty

let reduce_value se =
  match se with
  | Unknown | Ctor _ | Fn _ | FnApp (_, _, None :: _) | Prim _ ->
    (SESet.empty, SESet.empty)
  | PrimApp (prim, args) when front_arg_len args < prim.prim_arity ->
    (SESet.empty, SESet.empty)
  | PrimApp (prim, args) -> (
    let prim_args, tl = split_arg prim.prim_arity args in
    let value, seff = PrimResolution.value_prim (prim, prim_args) in
    match tl with
    | [] -> (value, seff)
    | _ ->
      SESet.fold
        (fun se (acc_value, acc_seff) ->
          let value', seff' = reduce_app se tl in
          (SESet.union acc_value value', SESet.union acc_seff seff'))
        value (SESet.empty, seff))
  | FnApp (param, bodies, Some hd :: tl) ->
    bodies |> List.iter evaluate_label;
    let value =
      bodies
      |> List.map (fun body ->
             if tl = [] then Var (Val body) else App (body, tl))
      |> SESet.of_list
    in
    let seff =
      bodies |> List.map (fun body -> Var (SideEff body)) |> SESet.of_list
    in
    update_sc (Var (Val param)) (SESet.singleton (Var (Val hd)));
    (value, seff)
  | App (e, arg) ->
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
    in
    (value, SESet.empty)
  | Var (Val e) ->
    let set = SESet.filter propagate (lookup_sc (Var (Val e))) in
    (set, SESet.empty)
  | Mem mem ->
    let set = SESet.filter propagate (lookup_sc (Mem mem)) in
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
  | Evaluated -> SESet.empty
  | _ ->
    failwith "Invalid side effect se"

let reduce_value_used_in_unknown se =
  match se with
  | Fn (arg, bodies) ->
    SESet.singleton (FnApp (arg, bodies, None :: []))
  | Ctor (Record, mems) | Ctor (Array, mems)->
    mems |> List.map (fun mem -> Mem mem) |> SESet.of_list
  | Ctor (_, labels) ->
    labels |> List.map (fun label -> Var (Val label)) |> SESet.of_list
  | FnApp (param, bodies, None :: tl) ->
    bodies |> List.iter evaluate_label;
    update_sc (Var (Val param)) (SESet.singleton Unknown);
    bodies
      |> List.map (fun body -> if tl = [] then Var (Val body) else App (body, tl))
      |> SESet.of_list
  | PrimApp (prim, args) when front_arg_len args < prim.prim_arity ->
    args
      |> List.filter_map (fun x -> x)
      |> List.map (fun label -> Var (Val label)) |> SESet.of_list
  | Unknown | Prim _ -> SESet.empty
  | App _ | FnApp _ | PrimApp _ | Var (Val _) | Id _ | Mem _ ->
    let value, _ = reduce_value se in
    value
  | _ ->
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
    lookup_sc (Var (Val e))
    |> SESet.iter (function
         | Ctor (Record, l) -> (
           try update_sc (Mem (List.nth l i)) set with _ -> ())
         | _ -> ())
  | UsedInUnknown ->
    let reduced =
      SESet.fold
        (fun se acc ->
          let value = reduce_value_used_in_unknown se in
          SESet.union value acc)
        set SESet.empty
    in
    update_sc x reduced
  | _ -> failwith "Invalid LHS"

let step_sc_for_pair (lhs, rhs) =
  match lhs with
  | Mem _ | Id _ ->
    let value, _ = reduce_value rhs in
    update_sc lhs value
  | Var (Val e) ->
    let value, seff = reduce_value rhs in
    update_sc (Var (Val e)) value;
    update_sc (Var (SideEff e)) seff
  | Var (SideEff _) ->
    let seff = reduce_seff rhs in
    update_sc lhs seff
  | Fld (e, (Record, Some i)) ->
    lookup_sc (Var (Val e))
    |> SESet.iter (function
         | Ctor (Record, l) -> (
           try update_sc (Mem (List.nth l i)) (SESet.singleton rhs)
           with _ -> ())
         | _ -> ())
  | UsedInUnknown ->
    let value = reduce_value_used_in_unknown rhs in
    update_sc lhs value
  | _ -> failwith "Invalid LHS"

let solve () =
  while not (worklist |> Worklist.is_empty) do
    let pair = worklist |> Worklist.pop in
    update_reverse pair;
    get_workitems pair
    |> WorkItemSet.iter (function
         | WorkPair (key, elt) -> step_sc_for_pair (key, elt)
         | WorkKey key -> step_sc_for_entry key)
  done

let hasSideEffect label =
  lookup_sc (Var (SideEff label)) |> SESet.mem SideEffect
