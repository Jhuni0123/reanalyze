open SetExpression

let get_context label = fst label

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
  | _prim, args ->
      update_sc UsedInUnknown (args |> List.map (fun arg -> Var (Val arg)) |> SESet.of_list);
      (SESet.singleton Unknown, SESet.singleton SideEffect)


