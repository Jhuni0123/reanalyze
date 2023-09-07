open SetExpression
open CL.Typedtree
open CL.Types

(* module Field = struct *)
(*   type t = F_Record of string | F_Tuple of int *)

(*   let compare = compare *)
(* end *)

(* module StringMap = Map.Make (String) *)


(* module FieldMap = Map.Make (Field) *)

type t =
  | Top
  | Bot
  | Ctor of t list CtorMap.t (* K1(L1, L2) + K2(L1, L2) *)
  | Func of t (* () -> L *)

let empty_ctor = Ctor CtorMap.empty

(* let variant lbl l : t = Construct (CtorMap.singleton (Variant lbl) [l]) *)
(* let field f l : t = Construct (CtorMap.singleton (Record f) [l]) *)
(* let construct cstr ls : t = Construct (CstrMap.singleton cstr ls) *)

(* let constructi cstr idx l : t = *)
(*   let ls = List.init (idx + 1) (function i when i = idx -> l | _ -> Bot) in *)
(*   Construct (CstrMap.singleton cstr ls) *)

let rec join a b =
  match (a, b) with
  | Top, _ | _, Top -> Top
  | Bot, x | x, Bot -> x
  | Ctor cs, Ctor cs' ->
    let rec join_list l1 l2 =
      match (l1, l2) with
      | [], [] -> []
      | [], _ -> l2
      | _, [] -> l1
      | hd1 :: tl1, hd2 :: tl2 -> join hd1 hd2 :: join_list tl1 tl2
    in
    let merged = CtorMap.merge (fun _ctor ls ls' ->
      match ls, ls' with
      | None, x | x, None -> x
      | Some ls, Some ls' -> Some (join_list ls ls')
      ) cs cs'
    in 
    Ctor merged
  | Func x, Func y -> Func (join x y)
  | _ -> Top

let rec meet a b =
  match (a, b) with
  | Top, x | x, Top -> x
  | Bot, _ | _, Bot -> Bot
  | Ctor cs, Ctor cs' ->
    let rec meet_list l1 l2 =
      match (l1, l2) with
      | hd1 :: tl1, hd2 :: tl2 -> meet hd1 hd2 :: meet_list tl1 tl2
      | _ -> []
    in
    let merged = CtorMap.merge (fun _ctor ls ls' ->
      match ls, ls' with
      | None, _ | _, None -> None
      | Some ls, Some ls' -> Some (meet_list ls ls')
      ) cs cs'
    in 
    Ctor merged
  | Func x, Func y -> Func (meet x y)
  | _ -> Bot

(* let variant_inv k l = *)
(*   match l with *)
(*   | Top -> Top *)
(*   | Bot -> Bot *)
(*   | Variant ks -> ( *)
(*     match StringMap.find_opt k ks with *)
(*     | None -> Bot *)
(*     | Some (Some l) -> l *)
(*     | Some None -> Bot) *)
(*   | _ -> Bot *)

(* let field_inv k l = *)
(*   match l with *)
(*   | Top -> Top *)
(*   | Bot -> Bot *)
(*   | Record fs -> ( *)
(*     match FieldMap.find_opt k fs with None -> Bot | Some l -> l) *)
(*   | _ -> Bot *)

(* let construct_inv cstr_desc idx l = *)
(*   match l with *)
(*   | Top -> Top *)
(*   | Bot -> Bot *)
(*   | Construct cs -> ( *)
(*     match CstrMap.find_opt cstr_desc cs with *)
(*     | None -> Bot *)
(*     | Some ls -> List.nth_opt ls idx |> Option.value ~default:Bot) *)
(*   | _ -> Bot *)

let rec equal l1 l2 =
  match (l1, l2) with
  | Top, Top -> true
  | Bot, Bot -> true
  | Ctor cs1, Ctor cs2 -> CtorMap.equal (List.equal equal) cs1 cs2
  | _ -> false

let rec controlledByPat (pat : pattern) =
  match pat.pat_desc with
  | Tpat_any -> Bot
  | Tpat_var _ -> Bot
  | Tpat_alias (pat, _, _) -> controlledByPat pat
  | Tpat_constant _ -> Top
  | Tpat_tuple pats ->
    Ctor (CtorMap.singleton Tuple (pats |> List.map controlledByPat))
  | Tpat_construct (_, cstr_desc, pats) ->
    Ctor (CtorMap.singleton (Construct cstr_desc.cstr_name) (pats |> List.map controlledByPat))
  | Tpat_variant (label, Some pat, _) ->
    Ctor (CtorMap.singleton (Variant label) [pat |> controlledByPat])
  | Tpat_variant (_, None, _) -> Top
  | Tpat_record (fields, _) ->
    let len =
      fields |> List.fold_left (fun acc (_, lbl_desc, _) -> max acc (lbl_desc.lbl_pos + 1)) 0
    in
    let arr = Array.make len Bot in
    fields
    |> List.iter (fun (_, lbl_desc, pat) ->
        let prev = Array.get arr lbl_desc.lbl_pos in
        let joined = join prev (controlledByPat pat) in
        Array.set arr lbl_desc.lbl_pos joined);
    Ctor (CtorMap.singleton Record (arr |> Array.to_list))
  | Tpat_array _ -> Top (* TODO: array *)
  | Tpat_or (pat1, pat2, _) ->
    join (controlledByPat pat1) (controlledByPat pat2)
  | Tpat_lazy _ -> Top
