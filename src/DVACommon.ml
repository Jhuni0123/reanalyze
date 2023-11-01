open CL.Typedtree

let deadAnnotation = "dead"

let liveAnnotation = "live"

module StringSet = Set.Make (String)

module Current = struct
  let cmtModName : string ref = ref ""
end

module Id = struct
  (* Ident.t is unique under a module file, except for the ident of top-level module (persistent). *)
  (* Then Ident.t with top-level module name is unique for whole codebase. *)
  type t = string * CL.Ident.t

  type summary = {
    id_loc : CL.Location.t;
  }

  let to_summary_tbl : (t, summary) Hashtbl.t = Hashtbl.create 10
  let to_summary id = Hashtbl.find to_summary_tbl id

  let createCmtModuleId modname : t =
    ("+", {name = modname; stamp = 0; flags = 0})

  let create ident : t =
    let ctx = !Current.cmtModName in
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

  let preprocess id loc =
    Hashtbl.add to_summary_tbl id { id_loc = loc }
end

module Label = struct
  type t = string * int

  let ctx (l : t) = fst l

  type value_expr_summary = {
    exp : expression;
    exp_labeled : expression;
    exp_type : CL.Types.type_expr;
    exp_loc : CL.Location.t;
    exp_context : string;
  }

  type module_expr_summary = {
    mod_exp : module_expr;
    mod_exp_labeled : module_expr;
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
    | Mem
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
    let e' = {e with exp_loc = new_loc label} in
    Hashtbl.add to_summary_tbl label
      (ValueExpr
         {
           exp = e;
           exp_labeled = e';
           exp_type = e.exp_type;
           exp_loc = e.exp_loc;
           exp_context = !Current.cmtModName;
         });
    e'

  let of_expression (e : expression) =
    let pos = e.exp_loc.loc_start in
    (pos.pos_fname, pos.pos_lnum)

  let preprocess_module_expr (me : module_expr) =
    let label = new_label !Current.cmtModName in
    let me' = {me with mod_loc = new_loc label} in
    Hashtbl.add to_summary_tbl label
      (ModExpr
         {
           mod_exp = me;
           mod_exp_labeled = me';
           mod_type = me.mod_type;
           mod_loc = me.mod_loc;
           mod_context = !Current.cmtModName;
         });
    me'

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

  let new_memory modname =
    let label = new_label modname in
    Hashtbl.add to_summary_tbl label Mem;
    label
end

type cmt_structure = {modname : string; structure : structure; label : Label.t}
let cmtStructures : cmt_structure list ref = ref []

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
  (* Set variable *)
  | Var of var
  | Id of Id.t
  (* Value *)
  | Unknown
  | Mem of memory_label
  | Prim of CL.Primitive.description
  | Fn of Label.t * Label.t list
  | App of Label.t * arg
  | FnApp of Label.t * Label.t list * arg
  | PrimApp of CL.Primitive.description * arg
  | Ctor of ctor * Label.t list
  | Fld of Label.t * fld
  (* Side Effect *)
  | SideEffect
  | UsedInUnknown
  | Evaluated

type value =
  | Top
  | V_Expr of Label.t
  | V_Id of Id.t
  | V_Mem of Label.t

let compare_value a b =
  match (a, b) with V_Id x, V_Id y -> Id.compare x y | _ -> compare a b

module ValueSet = Set.Make (struct
  type t = value

  let compare = compare_value
end)

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

  let equal a b = match (a, b) with Id x, Id y -> Id.equal x y | _ -> a = b
  let hash = function Id x -> Id.hash x | x -> Hashtbl.hash x
end)

let annotatedAsLive attributes =
  attributes
  |> Annotation.getAttributePayload (( = ) liveAnnotation)
  <> None

let rec front_arg_len = function
  | [] -> 0
  | None :: _ -> 0
  | Some _ :: tl -> front_arg_len tl + 1

let rec ids_in_pat (pat : pattern) =
  match pat.pat_desc with
  | Tpat_any | Tpat_constant _ -> []
  | Tpat_var (x, l) -> [(x, l.loc)]
  | Tpat_alias (p, x, l) -> ids_in_pat p @ [(x, l.loc)]
  | Tpat_tuple pats -> pats |> List.map ids_in_pat |> List.flatten
  | Tpat_construct (_, _, pats) -> pats |> List.map ids_in_pat |> List.flatten
  | Tpat_variant (_, None, _) -> []
  | Tpat_variant (_, Some p, _) -> ids_in_pat p
  | Tpat_record (fields, _) ->
    fields |> List.map (fun (_, _, p) -> ids_in_pat p) |> List.flatten
  | Tpat_array pats -> pats |> List.map ids_in_pat |> List.flatten
  | Tpat_lazy p -> ids_in_pat p
  | Tpat_or (lhs, rhs, _) -> ids_in_pat lhs @ ids_in_pat rhs
