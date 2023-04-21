open CL.Typedtree
open CL.Asttypes
open CL.Longident
open CL.Types

let rec pi i =
    match i with
    | 0 -> ()
    | _ as i -> print_string "  "; pi (i-1)

let ps = print_string
let pn = print_newline
let pe = print_endline

let psi i s = pi i; ps s
let pei i s = pi i; pe s

let print_loc (loc: CL.Location.t) =
  let (file, line, startchar) = CL.Location.get_pos_info loc.loc_start in
  let startchar =  startchar + 1 in 
  let endchar = loc.loc_end.pos_cnum - loc.loc_start.pos_cnum + startchar in
      Printf.printf "%s:%i:%i:%i:G_%B" file line (startchar-1) (endchar-1) (loc.loc_ghost)

let rec print_lident lid =
    match lid with
    | Lident id -> ps id
    | Ldot (a, b) -> print_lident a; ps "."; ps b
    | Lapply (_, _) -> ps ""

let rec print_list print_element delimeter l =
    match l with
    | [] -> ps ""
    | [e] -> print_element e
    | hd :: tl -> print_element hd; ps delimeter; print_list print_element delimeter tl

let print_ident (id: CL.Ident.t) =
  ps id.name;
  ps "#";print_int id.stamp

let rec print_pattern pat =
    match pat.pat_desc with
    | Tpat_any -> ps "_"
    | Tpat_var (id, loc) -> print_ident id; ps "@"; print_loc loc.loc
    | Tpat_alias (pat, id, loc) -> print_pattern pat; ps " as "; print_ident id
    | Tpat_constant _ -> ps "Tpat_constant"
    | Tpat_tuple (pats) ->
        ps "(";
        pats |> print_list print_pattern ",";
        ps ")"
    | Tpat_construct _ -> ps "Tpat_construct"
    | Tpat_variant _ -> ps "Tpat_variant"
    | Tpat_lazy _ -> ps "Tpat_lazy"
    | Tpat_array _ -> ps "Tpat_array"
    | Tpat_or (pat1, pat2, _) ->
        print_pattern pat1;
        ps " | ";
        print_pattern pat2
    | Tpat_record (fields, _) ->
        ps "{";
        fields |> print_list (fun (lid, lbl_desc, pat) -> ps lbl_desc.lbl_name; ps ": "; print_pattern pat) "; ";
        ps "}"

and print_value_binding i (vb: CL.Typedtree.value_binding) =
    print_pattern vb.vb_pat;
    pe " =";
    pi i;
    print_expression i vb.vb_expr

and str_rec_flag (flag: CL.Asttypes.rec_flag) =
    match flag with 
    | Recursive -> "rec " 
    | Nonrecursive -> ""

and print_expressionp i (expr: CL.Typedtree.expression) =
    match expr.exp_desc with
    | Texp_ident _ | Texp_constant _ -> print_expression i expr
    | _ -> print_expression i ~p:true expr

and print_path (p: CL.Path.t) =
    match p with
    | Pident id -> print_ident id
    | Pdot (p, s, i) -> print_path p; ps "."; ps s; ps "_"; print_int i;
    | Papply (p1, p2) -> print_path p1; ps "("; print_path p2; ps ")";

and print_module_expr me =
  (match me.mod_desc with
  | Tmod_ident (path, lid) -> ps "Tmod_ident "; print_path path; print_lident lid.txt; print_newline ()
  | Tmod_structure s -> print_structure s
  | Tmod_functor _ -> pe "Tmod_functor"
  | Tmod_apply (me1, me2, mc) ->
      pe "Tmod_apply";
      print_module_expr me1;
      print_module_expr me2
  | Tmod_constraint (me', _, _, _) -> pe "Tmod_constraint";
  print_module_expr me'
  | Tmod_unpack _ -> pe "Tmod_unpack"
  )

and print_expression i ?(p = false) (expr: CL.Typedtree.expression) =
    if p then ps "(";
    (match expr.exp_desc with
    | Texp_ident (path, lid, vd) ->
            ps "[";print_path path;ps"]";
            print_lident lid.txt;
            ps";";
            (match vd.val_kind with
            | Val_reg -> ps "reg"
            | Val_prim prim -> ps "prim ";ps prim.prim_name
            );
            ps";";
            print_loc vd.val_loc
    | Texp_constant (constant) ->
            (match constant with
            | Const_int n -> print_int n
            | Const_char c -> ps "'"; print_char c; ps"'"
            | Const_string (s, so) -> ps "\"";ps s; ps"\""
            | Const_float s -> ps s
            | _ -> ps "CONSTANT"
            );
    | Texp_let (rec_flag, vbs, exp) ->
            ps "let ";
            ps (str_rec_flag rec_flag);
            vbs |> print_list (print_value_binding (i+1)) "\n";
            pn ();
            pi i; pe "in";
            pi i; print_expression i exp;
    | Texp_function ({arg_label; param; cases; partial}) ->
            (* CL.Location.print_loc Format.std_formatter  expr.exp_loc; *)
            ps "function ";
            cases |> print_list (fun case ->
                ps "| ";
                print_pattern case.c_lhs;
                ps " -> ";
                print_expression i case.c_rhs
            ) "\n"
    | Texp_apply (exp, args) ->
            print_expressionp i exp;
            ps " ";
            args |> print_list (fun (al, eo) ->
                (match al with
                | Nolabel -> ps "-:"
                | Labelled l -> ps "~"; ps l; ps ":"
                | Optional l -> ps "~"; ps l; ps ":"
                );
                match eo with
                | None -> ps "-"
                | Some e -> print_expressionp 0 e
                ) " "
    | Texp_match (exp, cases, exc_cases, partial) -> ps "match"
    | Texp_try (exp, cases) -> ps "try"
    | Texp_tuple (exps) -> ()
    | Texp_construct (lid, cons_desc, exps) ->
        ps cons_desc.cstr_name;
        ps "(";
        exps |> print_list (print_expression 0) (", ");
        ps ")"
    | Texp_variant (label, expo) ->
        ps label;
        (match expo with
        | None -> ()
        | Some(exp) -> ps "("; print_expression 0 exp; ps ")"
        )
    | Texp_record ({fields; representation; extended_expression}) ->
            pe "{";
            (match extended_expression with
            | Some e -> pi (i+1); print_expression 0 e; ps " with"; pn ();
            | None -> ()
            );
            fields |> Array.iter (fun (label_desc, label_def) ->
                pi (i+1);
                ps label_desc.lbl_name;
                ps ": ";
                (match label_def with
                | Kept _ -> ps "<Kept>"
                | Overridden (_, e) -> print_expression (i+1) e
                );
                ps ";\n"
            );
            pi i;ps "}"
    | Texp_field (exp, lid, label_desc) ->
            print_expressionp 0 exp;
            ps ".";
            ps label_desc.lbl_name;
    | Texp_setfield (exp1, lid, label_desc, exp2) ->
            print_expression i exp1;
            ps ".";
            ps label_desc.lbl_name;
            ps " := ";
            print_expression 0 exp2;
    | Texp_array (exps) ->
            ps "ARRAY (";
            exps |> print_list (print_expression 0) ", ";
            ps ")"
    | Texp_ifthenelse (exp_cond, exp_then, expo_else) -> ps "IFTHENELSE()"
    | Texp_sequence (exp1, exp2) ->
            print_expression (i) exp1; pe ";";
            pi i; print_expression (i) exp2
    | Texp_while (exp_cond, exp_body) -> ps "WHILE()"
    | Texp_for (id, pat, exp_start, exp_end, dir, exp_body) ->
        ps "for "; print_ident id; print_loc pat.ppat_loc;
        ps " in ";
        print_expression 0 exp_start; ps " to ";
        print_expression 0 exp_end; pe " do";
        pi (i+1);print_expression (i+1) exp_body;
        print_newline ();
        pi i;pe "done";
    | Texp_send (exp, Tmeth_name meth, Some arg) ->
        ps "SEND(";
        pi (i+1);print_expression (i+1) exp;
        ps ",";
        print_expression (i+1) arg;
        ps ")"
    | Texp_send (exp, Tmeth_name meth, None) ->
        ps "SEND(";
        pi (i+1);print_expression (i+1) exp;
        ps ",";
        ps meth;
        ps ")"
    | Texp_new () -> ()
    | Texp_instvar () -> ()
    | Texp_setinstvar () -> ()
    | Texp_override () -> ()
    | Texp_letmodule (id, loc, mod_exp, exp) ->
        print_module_expr mod_exp;
        print_newline ();
        print_expression i exp
    | Texp_letexception (ext_cons, exp) -> ps "LETEXCEPTION()"
    | Texp_assert (exp) -> ps "ASSERT()"
    | Texp_lazy (exp) -> ps "LAZY()"
    | Texp_object () -> ()
    | Texp_pack (mod_exp) -> ps "PACK()"
    | Texp_unreachable -> ()
    | Texp_extension_constructor (lid, path) -> ps "EXT_CONSTRUCT()"
    );
    if p then ps ")"

and print_structure_item (structure_item: CL.Typedtree.structure_item) =
    match structure_item.str_desc with
    | Tstr_eval (exp, attr) ->
            pe "# Structure - eval";
            print_expression 0 exp;
            pn ();
            pn ()
    | Tstr_value (rec_flag, vbs) ->
            pe "# Structure - value binding";
            ps "let ";
            ps (str_rec_flag rec_flag);
            vbs |> List.iter (print_value_binding 0);
            pn ()
    | Tstr_primitive _ ->
        pe "# Structure - primitive"
    | Tstr_type _ ->
        pe "# Structure - type"
    | Tstr_typext _ ->
        pe "# Structure - typext"
    | Tstr_exception _ ->
        pe "# Structure - exception"
    | Tstr_module m ->
        pe "# Structure - module";
        pe m.mb_name.txt;
        print_module_expr m.mb_expr
    | Tstr_recmodule _ ->
        pe "# Structure - recmodule"
    | Tstr_open desc ->
        pe "# Structure - open";
        print_lident desc.open_txt.txt;
        pn ()
    | Tstr_class _ ->
        pe "# Structure - class"
    | Tstr_class_type _ ->
        pe "# Structure - class type"
    | Tstr_include _ ->
        pe "# Structure - include"
    | Tstr_attribute _ ->
        pe "# Structure - attribute"
    | Tstr_modtype _ ->
        pe "# Structure - modtype"

and print_structure structure = structure.str_items |> List.iter print_structure_item

let rec print_type (t: type_expr) =
    match t.desc with
    | Tvar None -> ps "Tvar None"
    | Tvar (Some(s)) -> ps "Tvar "; ps s
    | Tarrow (arg_label, t1, t2, commutable) -> print_type t1; ps " -> "; print_type t2;
    | Ttuple ts -> ps "("; print_list print_type ", " ts; ps ")"
    | Tconstr _ -> ps "Tconstr"
    | Tobject _ -> ps "Tobject"
    | Tfield _ -> ps "Tfield"
    | Tnil -> ps "Tnil"
    | Tlink t' -> ps "Tlink("; print_type t'; ps ")"
    | Tsubst _ -> ps "Tsubst"
    | Tvariant _ -> ps "Tvariant"
    | Tunivar _ -> ps "Tunivar"
    | Tpoly _ -> ps "Tpoly"
    | Tpackage _ -> ps "Tpackage"


let print_vd (vd: value_description) =
    print_type vd.val_type

let print_cmt_value_dependencies (vds: (value_description * value_description) list) =
    vds |> List.iter (fun (vdl, vdr) -> print_vd vdl; print_vd vdr)
