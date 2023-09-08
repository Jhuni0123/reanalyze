open SetExpression
open CL.Typedtree
open CL.Types

exception RuntimeError of string

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
    init_sc (Id (Id.create x)) [Var (Val e)];
    [(x, e)]
  | Tpat_alias (p, x, _) ->
    init_sc (Id (Id.create x)) [Var (Val e)];
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

let se_of_mb (mb : module_binding) =
  let label = Label.of_module_expr mb.mb_expr in
  init_sc (Id (Id.create mb.mb_id)) [Var (Val label)];
  ([(mb.mb_id, label)], [Var (SideEff label)])

let se_of_vb (vb : value_binding) =
  if vb.vb_attributes |> annotatedAsLive then
    ids_in_pat vb.vb_pat |> List.iter (fun (x, _) -> update_sc UsedInUnknown (SESet.singleton (Id (Id.create x))));
  let bindings = solve_pat vb.vb_pat (Label.of_expression vb.vb_expr) in
  (* let v = bindings |> List.map (fun (name, e) -> Ctor (Member name, [e])) in *)
  let seff = Var (SideEff (Label.of_expression vb.vb_expr)) in
  (bindings, [seff])

let list_split_flatten l =
  let a, b = List.split l in
  (List.flatten a, List.flatten b)

let se_of_struct_item (item : structure_item) =
  match item.str_desc with
  | Tstr_eval (e, _) -> ([], [Var (SideEff (Label.of_expression e))])
  | Tstr_value (_, vbs) -> vbs |> List.map se_of_vb |> list_split_flatten
  | Tstr_module mb -> se_of_mb mb
  | Tstr_recmodule mbs -> mbs |> List.map se_of_mb |> list_split_flatten
  | Tstr_include {incl_mod; incl_type} ->
    (* let value = Label.of_module_expr incl_mod in *)
    (* ([Var (Val value)], []) *)
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
    (* ([Var value], []) *)
  | Tstr_primitive vd ->
    let temp = Label.new_temp () in
    init_sc (Var (Val temp)) [Unknown];
    init_sc (Id (Id.create vd.val_id)) [Var (Val temp)];
    (* ([Ctor (Member (CL.Ident.name vd.val_id), [temp])], []) *)
    ([(vd.val_id, temp)], [])
  | _ -> ([], [])

module StringMap = Map.Make (String)

let se_of_struct str =
  let bindings, seff =
    str.str_items |> List.map se_of_struct_item |> list_split_flatten
  in
  let v =
    bindings
    |> List.map (fun (id, l) -> (CL.Ident.name id, l))
    |> List.to_seq |> StringMap.of_seq |> StringMap.bindings
    |> List.map (fun (name, label) -> Ctor (Member name, [label]))
  in
  (v, seff)

let se_of_expr expr =
  let solve_param (expr : Label.t) pattern : unit =
    solve_pat pattern expr |> ignore
  in
  match expr.exp_desc with
  | Texp_ident (_, _, {val_kind = Val_prim prim}) -> (
    match prim.prim_arity with 0 -> ([Unknown], []) | _ -> ([Prim prim], []))
  | Texp_ident (x, _, _) -> ([Var (Val (label_of_path x))], [])
  | Texp_constant _ -> ([], [])
  | Texp_let (_, vbs, e) ->
    let _, seff = vbs |> List.map se_of_vb |> list_split_flatten in
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
    let label = Label.of_expression exp in
    let ses =
      cases |> List.map (fun case -> Var (Val (Label.of_expression case.c_rhs)))
    in
    (Var (Val label) :: ses, [Var (SideEff label)])
  | Texp_tuple exps ->
    let v = [Ctor (Tuple, exps |> List.map Label.of_expression)] in
    let seff =
      exps |> List.map (fun e -> Var (SideEff (Label.of_expression e)))
    in
    (v, seff)
  | Texp_construct (_, _, []) -> ([], [])
  | Texp_construct (_, cstr_desc, exps) ->
    let v =
      [
        Ctor
          (Construct cstr_desc.cstr_name, exps |> List.map Label.of_expression);
      ]
    in
    let seff =
      exps |> List.map (fun e -> Var (SideEff (Label.of_expression e)))
    in
    (v, seff)
  | Texp_variant (lbl, Some exp) ->
    let v = [Ctor (Variant lbl, [Label.of_expression exp])] in
    let seff = [Var (SideEff (Label.of_expression exp))] in
    (v, seff)
  | Texp_variant (_, None) -> ([], [])
  | Texp_record {fields; extended_expression} ->
    let for_each_field
        ((lbl_desc : label_description), (lbl_def : record_label_definition)) =
      let mem = new_memory !Current.cmtModName in
      init_sc (Mem mem)
        (match lbl_def with
        | Kept _ -> (
          match extended_expression with
          | Some e ->
            [Fld (Label.of_expression e, (Record, Some lbl_desc.lbl_pos))]
          | None -> [])
        | Overridden (_, e) -> [Var (Val (Label.of_expression e))]);
      mem
    in
    let v =
      [Ctor (Record, fields |> Array.map for_each_field |> Array.to_list)]
    in
    let seff =
      match extended_expression with
      | Some e -> [Var (SideEff (Label.of_expression e))]
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
    let v = [Fld (Label.of_expression e, (Record, Some lbl.lbl_pos))] in
    let seff = [Var (SideEff (Label.of_expression e))] in
    (v, seff)
  | Texp_setfield (e1, _, lbl, e2) ->
    let val1 = Label.of_expression e1 in
    let val2 = Var (Val (Label.of_expression e2)) in
    init_sc (Fld (val1, (Record, Some lbl.lbl_pos))) [val2];
    ([], [SideEffect])
  | Texp_array exps ->
    let for_each_expr_val (expr : expression) =
      let mem = new_memory !Current.cmtModName in
      init_sc (Mem mem) [Var (Val (Label.of_expression expr))];
      mem
    in
    let v = [Ctor (Array, exps |> List.map for_each_expr_val)] in
    let seff =
      exps |> List.map (fun e -> Var (SideEff (Label.of_expression e)))
    in
    (v, seff)
  | Texp_ifthenelse (exp, exp_true, Some exp_false) ->
    let val1 = Var (Val (Label.of_expression exp_true)) in
    let val2 = Var (Val (Label.of_expression exp_false)) in
    let seff0 = Var (SideEff (Label.of_expression exp)) in
    let seff1 = Var (SideEff (Label.of_expression exp_true)) in
    let seff2 = Var (SideEff (Label.of_expression exp_false)) in
    ([val1; val2], [seff0; seff1; seff2])
  | Texp_ifthenelse (exp, exp_true, None) ->
    let seff0 = Var (SideEff (Label.of_expression exp)) in
    let seff1 = Var (SideEff (Label.of_expression exp_true)) in
    ([Var (Val (Label.of_expression exp_true))], [seff0; seff1])
  | Texp_sequence (exp1, exp2) ->
    let val2 = Var (Val (Label.of_expression exp2)) in
    let seff1 = Var (SideEff (Label.of_expression exp1)) in
    let seff2 = Var (SideEff (Label.of_expression exp2)) in
    ([val2], [seff1; seff2])
  | Texp_while (exp_cond, exp_body) ->
    let seff_cond = Var (SideEff (Label.of_expression exp_cond)) in
    let seff_body = Var (SideEff (Label.of_expression exp_body)) in
    ([], [seff_cond; seff_body])
  | Texp_for (x, _, exp1, exp2, _, exp_body) ->
    init_sc (Id (Id.create x)) [];
    let seff1 = Var (SideEff (Label.of_expression exp1)) in
    let seff2 = Var (SideEff (Label.of_expression exp2)) in
    let seff_body = Var (SideEff (Label.of_expression exp_body)) in
    ([], [seff1; seff2; seff_body])
  | Texp_letmodule (x, _, me, e) ->
    let val_m = Var (Val (Label.of_module_expr me)) in
    let val_e = Var (Val (Label.of_expression e)) in
    init_sc (Id (Id.create x)) [val_m];
    let seff_m = Var (SideEff (Label.of_module_expr me)) in
    let seff_e = Var (SideEff (Label.of_expression e)) in
    ([val_e], [seff_m; seff_e])
  | Texp_pack me ->
    ( [Var (Val (Label.of_module_expr me))],
      [Var (SideEff (Label.of_module_expr me))] )
  | Texp_send (_, _, None) -> ([Unknown], [SideEffect])
  | Texp_send (_, _, Some _) -> ([Unknown], [SideEffect])
  | Texp_letexception (_, e) ->
    let v = Var (Val (Label.of_expression e)) in
    let seff = Var (SideEff (Label.of_expression e)) in
    ([v], [seff])
  | Texp_lazy exp ->
    (* let temp = Label.new_temp () in *)
    (* ([Fn (temp, [Label.of_expression exp])], []) *)
    (* FIXME: handle lazy *)
    ( [Var (Val (Label.of_expression exp))],
      [Var (SideEff (Label.of_expression exp))] )
  | _ -> ([], [])

let se_of_module_expr (m : CL.Typedtree.module_expr) =
  match m.mod_desc with
  | Tmod_functor (x, _, _, me) ->
    let param = Label.new_param x in
    init_sc (Id (Id.create x)) [Var (Val param)];
    ([Fn (param, [Label.of_module_expr me])], [])
  | Tmod_ident (x, _) ->
    let x = label_of_path x in
    ([Var (Val x)], [])
  | Tmod_structure structure -> se_of_struct structure
  | Tmod_apply (func, arg, _) ->
    let v =
      [App (Label.of_module_expr func, [Some (Label.of_module_expr arg)])]
    in
    let seff_f = Var (SideEff (Label.of_module_expr func)) in
    let seff_arg = Var (SideEff (Label.of_module_expr arg)) in
    (v, [seff_f; seff_arg])
  | Tmod_constraint (m, _, _, _) ->
    ( [Var (Val (Label.of_module_expr m))],
      [Var (SideEff (Label.of_module_expr m))] )
  | Tmod_unpack (e, _) ->
    ( [Var (Val (Label.of_expression e))],
      [Var (SideEff (Label.of_expression e))] )

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
  | _ ->
    PrintSE.print_se se;
    failwith "Invalid side effect se"

let reduce_value_used_in_unknown se =
  match se with
  | Var (Val _) | Id _ -> SESet.filter propagate (lookup_sc se)
  | Fn (arg, bodies) ->
    SESet.singleton (FnApp (arg, bodies, None :: []))
  | Ctor (Record, mems) ->
    mems
    |> List.fold_left
         (fun acc mem ->
           let field_values = SESet.filter propagate (lookup_sc (Mem mem)) in
           SESet.union acc field_values)
         SESet.empty
  | Ctor (_, labels) ->
    labels
    |> List.fold_left
         (fun acc label ->
           let field_values =
             SESet.filter propagate (lookup_sc (Var (Val label)))
           in
           SESet.union acc field_values)
         SESet.empty
  | FnApp (param, bodies, None :: tl) ->
    update_sc (Var (Val param)) (SESet.singleton Unknown);
    bodies
      |> List.map (fun body -> if tl = [] then Var (Val body) else App (body, tl))
      |> SESet.of_list
  | PrimApp (prim, args) when front_arg_len args < prim.prim_arity ->
    args
      |> List.filter_map (fun x -> x)
      |> List.map (fun label -> Var (Val label)) |> SESet.of_list
  | Unknown | Prim _ -> SESet.empty
  | App _ | FnApp _ | PrimApp _ ->
    let value, _ = reduce_value se in
    value
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
