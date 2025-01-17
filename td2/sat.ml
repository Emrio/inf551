type var = int

type formula =
  | Var of var
  | And of formula * formula
  | Or of formula * formula
  | Not of formula
  | True
  | False

let rec subst v t = function
  | Var x when x = v -> t
  | And (a, b) -> And (subst v t a, subst v t b)
  | Or (a, b) -> Or (subst v t a, subst v t b)
  | Not a -> Not (subst v t a)
  | r -> r

let rec free_var = function
  | Var x -> Some (Var x)
  | Or (a, b) | And (a, b) -> (
      match (free_var a, free_var b) with
      | Some (Var x), _ -> Some (Var x)
      | _, Some (Var x) -> Some (Var x)
      | _ -> None)
  | Not a -> free_var a
  | _ -> None

let rec eval = function
  | Var _ -> failwith "eval: formula has free variable"
  | True -> true
  | False -> false
  | And (a, b) -> eval a && eval b
  | Or (a, b) -> eval a || eval b
  | Not a -> not (eval a)

let rec sat f =
  match free_var f with
  | Some (Var x) -> sat (subst x True f) || sat (subst x False f)
  | _ -> eval f

let () =
  let x = Var 0 in
  let x' = Not x in
  let y = Var 1 in
  let y' = Not y in
  let a = And (And (Or (x, y), Or (x', y)), Or (x', y')) in
  let b = And (And (Or (x, y), Or (x', y)), And (Or (x, y'), Or (x', y'))) in
  assert (sat a);
  assert (not (sat b))

type literal = bool * var (* false means negated *)

type clause = literal list

type cnf = clause list

let rec list_mem x = function
  | [] -> false
  | t :: _ when x = t -> true
  | _ :: c -> list_mem x c

(* | t::c -> x = t || list_mem x c *)

let () =
  assert (list_mem 2 [ 1; 2; 3 ]);
  assert (not (list_mem 5 [ 1; 2; 3 ]));
  assert (not (list_mem 1 []))

let rec list_map mapper = function
  | [] -> []
  | t :: c -> mapper t :: list_map mapper c

let () =
  assert (list_map (fun x -> 2 * x) [ 1; 2; 3 ] = [ 2; 4; 6 ]);
  assert (list_map (fun _ -> ()) [] = [])

let rec list_filter pred = function
  | [] -> []
  | t :: c when pred t -> t :: list_filter pred c
  | _ :: c -> list_filter pred c

let () =
  let even x = x mod 2 = 0 in
  assert (list_filter even [ 1; 2; 3; 4; 6 ] = [ 2; 4; 6 ])

let subst_cnf x v lst =
  let doesnt_have_vx a = not (list_mem (v, x) a) in
  let lst' = list_filter doesnt_have_vx lst in
  let isnt_not_x a = a <> (not v, x) in
  let lst'' = list_map (list_filter isnt_not_x) lst' in
  lst''

let print_var = function
  | true, x -> print_int x
  | false, x ->
      print_string "!";
      print_int x

let rec print_clause = function
  | [] -> print_string "(empty clause = false)"
  | [ a ] -> print_var a
  | a :: b :: rem ->
      print_var a;
      print_string " \\/ ";
      print_clause (b :: rem)

let rec print_cnf = function
  | [] -> print_string "(empty cnf = true)"
  | [ a ] ->
      print_string "(";
      print_clause a;
      print_string ")"
  | a :: b :: rem ->
      print_string "(";
      print_clause a;
      print_string ") /\\ ";
      print_cnf (b :: rem)

let rec dpll = function
  | [] -> true
  | [] :: _ -> false
  | ((v, x) :: rem_clause) :: rem_cnf ->
      dpll (subst_cnf x v rem_cnf)
      (* use "x" *) || dpll (subst_cnf x (not v) (rem_clause :: rem_cnf))

(* use "not x" *)

let () =
  let x = (true, 0) in
  let x' = (false, 0) in
  let y = (true, 1) in
  let y' = (false, 1) in
  let a = [ [ x; y ]; [ x'; y ]; [ x'; y' ] ] in
  let b = [ [ x; y ]; [ x'; y ]; [ x; y' ]; [ x'; y' ] ] in
  assert (dpll a);
  assert (not (dpll b))

let rec unit = function
  | [] -> raise Not_found
  | [ lit ] :: _ -> lit
  | _ :: rem -> unit rem

let () =
  let x = (true, 0) in
  let y = (true, 1) in
  let y' = (false, 1) in
  assert (unit [ [ x; y ]; [ x ]; [ y; y' ] ] = x)

let rec list_flat = function
  | [] -> []
  | [] :: rem -> list_flat rem
  | (x :: rem') :: rem -> x :: list_flat (rem' :: rem)

let pure cnf =
  let all_litterals = list_flat cnf in
  let rec aux a =
    match a with
    | [] -> raise Not_found
    | (v, x) :: rem when list_mem (not v, x) all_litterals -> aux rem
    | (v, x) :: _ -> (v, x)
  in
  aux all_litterals

let dpll2 = function
  | [] -> true
  | cnf when list_mem [] cnf -> false
  | cnf -> (
      let cnf' =
        try
          let v, x = unit cnf in
          subst_cnf x v cnf
        with Not_found -> cnf
      in
      let cnf'' =
        try
          let v, x = pure cnf in
          subst_cnf x v cnf'
        with Not_found -> cnf'
      in
      match cnf'' with
      | [] -> true
      | [] :: _ -> false
      | cnf'' when list_mem [] cnf'' -> false
      | ((v, x) :: rem_clause) :: rem_cnf ->
          dpll (subst_cnf x v rem_cnf)
          (* use "x" *) || dpll (subst_cnf x (not v) (rem_clause :: rem_cnf))
      (* use "not x" *))

let () =
  let x = (true, 0) in
  let x' = (false, 0) in
  let y = (true, 1) in
  let y' = (false, 1) in
  let a = [ [ x; y ]; [ x'; y ]; [ x'; y' ] ] in
  let b = [ [ x; y ]; [ x'; y ]; [ x; y' ]; [ x'; y' ] ] in
  assert (dpll2 a);
  assert (not (dpll2 b))

(** Parse a CNF file. *)
let parse f : cnf =
  let load_file f =
    let ic = open_in f in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Bytes.to_string s
  in
  let f = load_file f in
  let f = String.map (function '\t' -> ' ' | c -> c) f in
  let f = String.split_on_char '\n' f in
  let f = List.map (String.split_on_char ' ') f in
  let f = List.filter (function "c" :: _ | "p" :: _ -> false | _ -> true) f in
  let f = List.flatten f in
  let aux (a, c) = function
    | "" -> (a, c)
    | "0" -> (c :: a, [])
    | n ->
        let n = int_of_string n in
        let x = if n < 0 then (false, -n) else (true, n) in
        (a, x :: c)
  in
  fst (List.fold_left aux ([], []) f)

let () = if Array.length Sys.argv > 1 then assert (dpll2 (parse Sys.argv.(1)))

let cnf f : cnf =
  let rec aux v f =
    match (v, f) with
    | v, True -> [ [ (v, -1) ] ]
    | v, False -> [ [ (not v, -1) ] ]
    | v, Var x -> [ [ (v, x) ] ]
    | v, Not x -> aux (not v) x
    | true, Or (a, b) ->
        let rec distrib a b =
          match (a, b) with
          | [], _ -> []
          | _, [] -> []
          | a :: rem, b -> List.map (fun x -> a @ x) b @ distrib rem b
        in
        distrib (aux true a) (aux true b)
    | false, Or (a, b) -> aux false a @ aux false b
    | true, And (a, b) -> aux true a @ aux true b
    | false, And (a, b) -> aux true (Or (Not a, Not b))
  in
  aux true f
