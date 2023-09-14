open CL.Typedtree
open CL.Types
open Common
open DVACommon

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

let preprocess_mapper =
  let super = CL.Tast_mapper.default in
  let pat self p =
    ids_in_pat p
    |> List.iter (fun (id, loc) -> Id.preprocess (Id.create id) loc);
    super.pat self p
  in
  let module_binding self mb =
    Id.preprocess (Id.create mb.mb_id) mb.mb_name.loc;
    super.module_binding self mb
  in
  let value_description self vd =
    Id.preprocess (Id.create vd.val_id) vd.val_name.loc;
    super.value_description self vd
  in
  let expr self e =
    (match e.exp_desc with
    | Texp_for (x, ppat, _, _, _, _) ->
      Id.preprocess (Id.create x) ppat.ppat_loc
    | Texp_letmodule (x, l, _, _) -> Id.preprocess (Id.create x) l.loc
    | _ -> ());
    let e' = Label.preprocess_expression e in
    super.expr self e'
  in
  let module_expr self me =
    (match me.mod_desc with
    | Tmod_functor (x, l, _, _) -> Id.preprocess (Id.create x) l.loc
    | _ -> ());
    let me' = Label.preprocess_module_expr me in
    super.module_expr self me'
  in
  {super with pat; module_binding; value_description; expr; module_expr}

let processCmtStructure modname (structure : CL.Typedtree.structure) =
  let structure = structure |> preprocess_mapper.structure preprocess_mapper in
  let traverse = Closure.traverse_init_sc in
  structure |> traverse.structure traverse |> ignore;
  let label = Closure.init_cmt_structure modname structure in
  cmtStructures := {structure; label; modname} :: !cmtStructures

let processCmt (cmt_infos : CL.Cmt_format.cmt_infos) =
  Current.cmtModName := cmt_infos.cmt_modname;
  match cmt_infos.cmt_annots with
  | Interface _ -> ()
  | Implementation structure ->
    processCmtStructure cmt_infos.cmt_modname structure
  | _ -> ()

let isDeadExpr label =
   ValueDependency.isDeadValue (V_Expr label)
   && not (label |> Closure.hasSideEffect)

let collectDeadValuesMapper addDeadValue =
  let addDeadExpr label = addDeadValue (V_Expr label) in
  let super = CL.Tast_mapper.default in
  let pat self p =
    ids_in_pat p |> List.iter (fun (x, _) ->
      let v = ValueDependency.id x in
      if v |> ValueDependency.isDeadValue then addDeadValue v
    );
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
    (* let label = me |> Label.of_module_expr in *)
    (* if label |> isDeadExpr then ( *)
    (*   addDeadExpr label; *)
    (*   me) *)
    (* else *)
    super.module_expr self me
  in
  {super with expr; module_expr; pat}

let collectDeadValues cmts =
  let deads = ref ValueSet.empty in
  let addDeadValue v = deads := !deads |> ValueSet.add v in
  let addDeadExpr label = addDeadValue (V_Expr label) in
  let mapper = collectDeadValuesMapper addDeadValue in
  cmts
  |> List.iter (fun {structure; label; modname} ->
         if isDeadExpr label then addDeadExpr label
         else (
           Current.cmtModName := modname;
           mapper.structure mapper structure |> ignore));
  !deads

module FileLocationPrinter = struct
  type line = string

  let currentFile = ref ""

  let currentFileLines = (ref [||] : line array ref)

  let readFile fileName =
    let channel = open_in fileName in
    let lines = ref [] in
    let rec loop () =
      let line = input_line channel in
      lines := line :: !lines;
      loop ()
      [@@raises End_of_file]
    in
    try loop ()
    with End_of_file ->
      close_in_noerr channel;
      !lines |> List.rev |> Array.of_list

  let writeFile fileName lines =
    if fileName <> "" && !Common.Cli.write then (
      let channel = open_out fileName in
      let lastLine = Array.length lines in
      lines
      |> Array.iteri (fun n line ->
             output_string channel line;
             if n < lastLine - 1 then output_char channel '\n');
      close_out_noerr channel)

  let print ~ppf (loc: CL.Location.t) =
    let (fileName, lineNumber, startIndex) = CL.Location.get_pos_info loc.loc_start in
    if Sys.file_exists fileName then (
      if fileName <> !currentFile then (
        writeFile !currentFile !currentFileLines;
        currentFile := fileName;
        currentFileLines := readFile fileName);
      match !currentFileLines.(lineNumber-1) with
      | line -> (
        let endIndex = loc.loc_end.pos_cnum - loc.loc_start.pos_cnum + startIndex in
        let underline = line |> String.mapi (fun i _ -> if startIndex <= i && i < endIndex then '-' else ' ') in
        let continue = if line |> String.length < endIndex then " (continued...)" else "" in
        Format.fprintf ppf "  <-- line %d@.  %s@.  %s@." loc.loc_start.pos_lnum line (underline ^ continue)
      )
      | exception Invalid_argument _ ->
        Format.fprintf ppf "  <-- Can't find line %d@." loc.loc_start.pos_lnum)
    else Format.fprintf ppf "  <-- Can't find file@."
end

let warning ~ppf ~(loc : CL.Location.t) name message =
  if Suppress.filter loc.loc_start then (
    let open Log_ in
    let body ppf () = Format.fprintf ppf "%s" message in
    Stats.count name;
    Format.fprintf ppf "@[<v 2>@,%a@,%a@,%a@]@." Color.info name Loc.print loc
      body ());
    FileLocationPrinter.print ~ppf loc

let report v ~ppf =
  match v with
  | V_Expr label -> (
    match label |> Label.to_summary with
    | ValueExpr e ->
      if not e.exp_loc.loc_ghost then (
        let name = "Warning Dead Expression" in
        let message = "This expression is evaluated as useless value and has no side effect" in
        warning ~ppf ~loc:e.exp_loc name message)
    | _ -> ())
  | V_Id id ->
    let summary = Id.to_summary id in
    if not summary.id_loc.loc_ghost then (
      let name = "Warning Dead Variable" in
      let message = "This variable always has useless value" in
      warning ~ppf ~loc:summary.id_loc name message)
  | _ -> ()

let reportDead ~ppf =
  if !Cli.debug then Log_.item "Solving Set-Closure@.";
  Closure.solve ();
  if !Cli.debug then Log_.item "Collecting Dependencies@.";
  ValueDependency.collect ();
  if !Cli.debug then Log_.item "Solving Dependencies@.";
  ValueDependency.solve ();
  if !Cli.debug then Log_.item "Done.@.";
  collectDeadValues !cmtStructures |> ValueSet.iter (fun v -> report v ~ppf)
