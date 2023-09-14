open DVACommon

type t =
  | Top
  | Bot
  | Ctor of t list CtorMap.t (* K1(L1, L2) + K2(L1, L2) *)
  | Func of t (* () -> L *)

let empty_ctor = Ctor CtorMap.empty

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

let rec equal l1 l2 =
  match (l1, l2) with
  | Top, Top -> true
  | Bot, Bot -> true
  | Ctor cs1, Ctor cs2 -> CtorMap.equal (List.equal equal) cs1 cs2
  | _ -> false
