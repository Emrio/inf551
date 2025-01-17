type prog =
  | Bool of bool
  | Int of int
  | Add of prog * prog
  | Lt of prog * prog
  | If of prog * prog * prog
  | Prod of prog * prog
  | Fst of prog
  | Snd of prog
  | Unit

type typ = TBool | TInt | TProd of typ * typ | TUnit

exception Type_error

let rec infer = function
  | Bool x -> TBool
  | Int x -> TInt
  | Add (x, y) -> (
      match (infer x, infer y) with TInt, TInt -> TInt | _ -> raise Type_error)
  | Lt (x, y) -> (
      match (infer x, infer y) with
      | TInt, TInt -> TBool
      | _ -> raise Type_error)
  | If (x, y, z) -> (
      match (infer x, infer y, infer z) with
      | TBool, TInt, TInt -> TInt
      | TBool, TBool, TBool -> TBool
      | _ -> raise Type_error)
  | Prod (x, y) -> TProd (infer x, infer y)
  | Fst x -> ( match infer x with TProd (a, _) -> a | _ -> raise Type_error)
  | Snd x -> ( match infer x with TProd (_, b) -> b | _ -> raise Type_error)
  | Unit -> TUnit

let typable a =
  try
    ignore (infer a);
    true
  with Type_error -> false

;;
typable (If (Lt (Add (Int 1, Int 2), Int 3), Int 4, Int 5))

;;
typable (Add (Int 1, Bool false))

;;
typable (If (Bool true, Int 1, Bool false))

;;
typable (Prod (Int 1, Bool false))

let rec reduce = function
  | Add (Int n1, Int n2) -> Some (Int (n1 + n2))
  | Add (p1, p2) -> (
      match (reduce p1, reduce p2) with
      | Some r1, _ -> Some (Add (r1, p2))
      | _, Some r2 -> Some (Add (p1, r2))
      | None, None -> None)
  | Lt (Int n1, Int n2) -> Some (Bool (n1 < n2))
  | Lt (p1, p2) -> (
      match (reduce p1, reduce p2) with
      | Some r1, _ -> Some (Lt (r1, p2))
      | _, Some r2 -> Some (Lt (p1, r2))
      | None, None -> None)
  | If (Bool result, a, b) -> Some (if result then a else b)
  | If (p, p1, p2) -> (
      match reduce p with Some r -> Some (If (r, p1, p2)) | None -> None)
  | Prod (p1, p2) -> (
      match (reduce p1, reduce p2) with
      | Some r1, _ -> Some (Prod (r1, p2))
      | _, Some r2 -> Some (Prod (p1, r2))
      | None, None -> None)
  | Fst (Prod (p1, _)) -> Some p1
  | Snd (Prod (_, p2)) -> Some p2
  | _ -> None

let rec normalize p = match reduce p with None -> p | Some r -> normalize r

let my_prog = If (Lt (Add (Int 1, Add (Int 2, Int 3)), Int 4), Bool false, Int 5)

;;
normalize my_prog

let rec preduce = function
  | Add (Int n1, Int n2) -> Int (n1 + n2)
  | Add (p1, p2) ->
      let r1 = preduce p1 and r2 = preduce p2 in
      Add (r1, r2)
  | Lt (Int n1, Int n2) -> Bool (n1 < n2)
  | Lt (p1, p2) ->
      let r1 = preduce p1 and r2 = preduce p2 in
      Lt (r1, r2)
  | If (Bool result, a, b) -> preduce (if result then a else b)
  | If (p, p1, p2) ->
      let r = preduce p and r1 = preduce p1 and r2 = preduce p2 in
      If (r, r1, r2)
  | Prod (p1, p2) ->
      let r1 = preduce p1 and r2 = preduce p2 in
      Prod (r1, r2)
  | Fst (Prod (p1, _)) -> p1
  | Snd (Prod (_, p2)) -> p2
  | p -> p

let rec pnormalize p =
  match preduce p with r when r <> p -> pnormalize r | _ -> p

;;
pnormalize my_prog

let my_pair = Prod (Int 3, Int 2)

let my_prod_2 = Prod (Snd my_pair, Fst my_pair)
