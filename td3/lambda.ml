type var = string

type t = Var of var | App of t * t | Abs of var * t

let rec to_string = function
  | Var x -> x
  | App (t, u) -> "(" ^ to_string t ^ " " ^ to_string u ^ ")"
  | Abs (x, u) -> "(λ" ^ x ^ "." ^ to_string u ^ ")"

let () =
  print_endline (to_string (Abs ("x", App (Var "y", Var "x"))));
  print_endline (to_string (App (Abs ("x", Var "y"), Var "x")))

let rec has_fv x = function
  | Var y -> x = y
  | App (t, u) -> has_fv x t || has_fv x u
  | Abs (y, t) -> x <> y && has_fv x t

let () =
  let t = App (Var "x", Abs ("y", App (Var "y", Var "z"))) in
  print_endline (to_string t);
  assert (has_fv "x" t);
  assert (not (has_fv "y" t));
  assert (has_fv "z" t);
  assert (not (has_fv "w" t))

let n = ref (-1)

let fresh () =
  incr n;
  "x" ^ string_of_int !n

let rec sub x u = function
  | Var y when x = y -> u
  | App (t, t') -> App (sub x u t, sub x u t')
  | Abs (y, t) ->
      if x = y || has_fv y u then
        let y' = fresh () in
        Abs (y', sub x u (sub y (Var y') t))
      else Abs (y, sub x u t)
  | t -> t

let () =
  let t = App (Var "x", Abs ("y", Var "x")) in
  let i = Abs ("x", Var "x") in
  let ti = App (Abs ("x", Var "x"), Abs ("y", Abs ("x", Var "x"))) in
  assert (sub "x" i t = ti);
  print_endline (to_string (Abs ("y", Var "x")));
  print_endline (to_string (Abs ("y", Var "y")));
  print_endline (to_string (sub "x" (Var "y") (Abs ("y", Var "x"))));
  assert (not (sub "x" (Var "y") (Abs ("y", Var "x")) = Abs ("y", Var "y")))

let rec red = function
  | App (Abs (x, t), u) -> Some (sub x u t)
  | Abs (x, t) -> (
      match red t with None -> None | Some t' -> Some (Abs (x, t')))
  | App (t, u) -> (
      match (red t, red u) with
      | Some t', _ -> Some (App (t', u))
      | _, Some u' -> Some (App (t, u'))
      | _ -> None)
  | _ -> None

let rec normalize t = match red t with None -> t | Some t' -> normalize t'

let reduction t =
  print_string "   ";
  print_endline (to_string t);
  let rec aux = function
    | None -> 0
    | Some t' ->
        print_string "-> ";
        print_endline (to_string t');
        1 + aux (red t')
  in

  print_endline ("Total: " ^ string_of_int (aux (red t)))

let _ =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  reduction (App (id2, id2))

let rec alpha t u =
  match (t, u) with
  | Var x, Var y -> x = y
  | App (t1, t2), App (u1, u2) -> alpha t1 u1 && alpha t2 u2
  | Abs (x, t1), Abs (y, u1) ->
      let z = fresh () in
      alpha (sub x (Var z) t1) (sub y (Var z) u1)
  | _ -> false

let () =
  assert (alpha (Abs ("x", Var "x")) (Abs ("y", Var "y")));
  assert (not (alpha (Abs ("x", Var "x")) (Abs ("x", Var "y"))))

let eq t u = alpha (normalize t) (normalize u)

let () =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  assert (eq (App (id2, id2)) id2)

let () =
  let t = App (Abs ("x", Abs ("y", Var "x")), Var "y") in
  print_endline (to_string (normalize t));
  assert (eq t (Abs ("z", Var "y")))

let id = Abs ("x", Var "x")

let btrue = Abs ("x", Abs ("y", Var "x"))

let bfalse = Abs ("x", Abs ("y", Var "y"))

let rec abss vars t = match vars with [] -> t | x :: rem -> Abs (x, abss rem t)

let () =
  let t = Var "t" in
  assert (abss [ "x"; "y"; "z" ] t = Abs ("x", Abs ("y", Abs ("z", t))))

let apps terms =
  let rec aux = function
    | [] -> failwith "apps [] not allowed"
    | [ t ] -> t
    | t :: rem -> App (aux rem, t)
  in
  aux (List.rev terms)

let () =
  let t = Var "t" in
  let u = Var "u" in
  let v = Var "v" in
  let w = Var "w" in
  assert (apps [ t; u; v; w ] = App (App (App (t, u), v), w))

let bif = abss [ "b"; "x"; "y" ] (apps [ Var "b"; Var "x"; Var "y" ])

let () =
  let t = Var "t" in
  let u = Var "u" in
  assert (eq (apps [ bif; btrue; t; u ]) t);
  assert (eq (apps [ bif; bfalse; t; u ]) u)

let nat n =
  abss [ "f"; "x" ]
    (apps (List.init (n + 1) (fun m -> if m = n then Var "x" else Var "f")))

let nat n =
  let rec aux = function 0 -> Var "x" | n -> App (Var "f", aux (n - 1)) in
  abss [ "f"; "x" ] (aux n)

let zero = nat 0

let one = nat 1

let two = nat 2

let three = nat 3

let succ =
  abss [ "n"; "f"; "x" ] (App (Var "f", apps [ Var "n"; Var "f"; Var "x" ]))

let () = assert (eq (apps [ succ; nat 5 ]) (nat 6))

let add =
  abss [ "m"; "n"; "f"; "x" ]
    (apps [ Var "m"; Var "f"; apps [ Var "n"; Var "f"; Var "x" ] ])

let () = assert (eq (apps [ add; nat 6; nat 5 ]) (nat 11))

let mul =
  abss [ "m"; "n"; "f"; "x" ]
    (apps [ Var "m"; apps [ Var "n"; Var "f" ]; Var "x" ])

let () = assert (eq (apps [ mul; nat 3; nat 4 ]) (nat 12))

(* Number of reductions: \propto m *)
let () = reduction (apps [ mul; nat 3; nat 4 ])

let iszero = Abs ("n", apps [ Var "n"; Abs ("z", bfalse); btrue ])

let () =
  assert (eq (apps [ iszero; nat 5 ]) bfalse);
  assert (eq (apps [ iszero; nat 0 ]) btrue)

let pair = abss [ "x"; "y"; "b" ] (apps [ bif; Var "b"; Var "x"; Var "y" ])

let fst = Abs ("p", App (Var "p", btrue))

let snd = Abs ("p", App (Var "p", bfalse))

let () =
  let t = Var "t" in
  let u = Var "u" in
  assert (eq (apps [ fst; apps [ pair; t; u ] ]) t);
  assert (eq (apps [ snd; apps [ pair; t; u ] ]) u)

let rec fib_naive = function
  | 0 -> 0
  | 1 -> 1
  | n -> fib_naive (n - 1) + fib_naive (n - 2)

let () = assert (fib_naive 10 = 55)

let fib_fun = function f, f' -> (f', f + f')

let fib n =
  let rec aux t = function 0 -> Stdlib.fst t | n -> aux (fib_fun t) (n - 1) in
  aux (0, 1) n

let () = assert (fib 10 = 55)

let pred_fun =
  Abs ("p", apps [ pair; App (snd, Var "p"); App (succ, App (snd, Var "p")) ])

let () =
  assert (
    eq
      (apps [ pred_fun; apps [ pair; nat 1; nat 5 ] ])
      (apps [ pair; nat 5; nat 6 ]))

let pred =
  Abs ("n", App (fst, apps [ Var "n"; pred_fun; apps [ pair; zero; zero ] ]))

let () =
  assert (eq (apps [ pred; nat 11 ]) (nat 10));
  assert (eq (apps [ pred; nat 0 ]) (nat 0))

let substract = abss [ "m"; "n" ] (apps [ Var "n"; pred; Var "m" ])

let () = assert (eq (apps [ substract; nat 14; nat 5 ]) (nat 9))

let fact_fun f n = if n = 0 then 1 else n * f (n - 1)

let rec fix f n = f (fix f) n

let fact = fix fact_fun

let () = assert (fact 5 = 120)

let fixpoint =
  let aux = Abs ("x", App (Var "f", App (Var "x", Var "x"))) in
  Abs ("f", App (aux, aux))

let factorial =
  apps
    [
      fixpoint;
      abss [ "f"; "n" ]
        (apps
           [
             bif;
             App (iszero, Var "n");
             one;
             apps [ mul; Var "n"; App (Var "f", App (pred, Var "n")) ];
           ]);
    ]

let () = assert (eq (App (factorial, nat 4)) (nat 24))

let etaeq t u =
  let rec aux t u =
    match (t, u) with
    | Var x, Var y -> x = y
    | App (t1, t2), App (u1, u2) -> aux t1 u1 && aux t2 u2
    | Abs (x, t1), Abs (y, u1) ->
        let z = fresh () in
        aux (sub x (Var z) t1) (sub y (Var z) u1)
    | Abs (x, App (v, y)), w | w, Abs (x, App (v, y)) -> Var x = y && aux v w
    | _ -> false
  in
  aux (normalize t) (normalize u)

let () = assert (eq (apps [ substract; nat 14; nat 5 ]) (nat 9))
