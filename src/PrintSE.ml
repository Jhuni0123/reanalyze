open SetExpression

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
  match Label.to_summary label with
  | ValueExpr e -> prerr_string ("Expr:" ^ modname ^ "_" ^ string_of_int i); prerr_string " @ "; print_code_loc e.exp_loc
  | ModExpr m -> prerr_string ("Mod:" ^ modname ^ "_" ^ string_of_int i); prerr_string " @ "; print_code_loc m.mod_loc
  | Tmp -> prerr_string ("Temp:" ^ modname ^ "_" ^ string_of_int i)
  | FnParam id -> prerr_string ("Param:" ^ modname ^ "_" ^ string_of_int i ^ CL.Ident.unique_name id)
  | Path p -> prerr_string ("Path:" ^ modname ^ "_" ^ string_of_int i ^ CL.Path.name p)
  | CmtModule modname -> prerr_string ("Module:" ^ modname ^ ":" ^ string_of_int i)
  (* | exception Not_found -> prerr_string ("label?_" ^ modname ^ "_" ^ string_of_int i) *)

let print_var = function
  | Val label -> prerr_string "Val ("; print_summary label; prerr_string ")"
  | SideEff label -> prerr_string "SideEff ("; print_summary label; prerr_string ")"

let print_param = function
  | None -> ()
  | Some (x, _) -> prerr_string (CL.Ident.name x)

let print_ctor = function
  | Variant k -> prerr_string k
  | Construct cstr -> prerr_string cstr
  | Record -> prerr_string "Record"
  | Tuple -> prerr_string "Tuple"
  | Member name -> prerr_string name
  | Array -> prerr_string "Array"

let print_arg = function
  | None -> prerr_string "-"
  | Some a -> print_summary a

let rec print_se : se -> unit = function
  | Unknown -> prerr_string "Unknown"
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
    (match k with
    | Record -> print_list print_mem ";" arr
    | _ -> print_list print_summary ";" arr
    );
    (* print_list_with_separator arr ";"; *)
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
  | Mem (ctx, i) -> prerr_string ("!ℓ_" ^ ctx ^ "_" ^ string_of_int i)
  | Id x -> prerr_string (x |> Id.to_string)
  | SideEffect -> prerr_string "φ"
  | AppliedToUnknown -> prerr_string "AoU"

and print_ses (xs : se list) =
  prerr_string "[";
  List.iter print_se xs;
  prerr_string "]"

and print_live l =
  let ps = prerr_string in
  match l with
  | Live.Top -> ps "⊤"
  | Bot -> ps "⊥"
  | Ctor cs ->
    cs |> CtorMap.bindings
    |> print_list
         (fun (ctor, v) ->
           print_ctor ctor;
           ps "(";
           v |> print_list print_live ",";
           ps ")")
         "+"

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

let show_sc_tbl (tbl : SESet.t SETbl.t) =
  SETbl.iter
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
        Live.get key |> print_live;
        prerr_newline ();
        prerr_newline ();
        ))
    tbl

let filter_closure = function
  | Fn (_, _) | App (_, None :: _) | PrimApp _ | Prim _ -> true
  | _ -> false

let show_closure_analysis tbl =
  prerr_endline "Closure analysis:";
  SETbl.iter
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


