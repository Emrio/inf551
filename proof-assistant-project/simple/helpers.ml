open Expr

let rec string_of_ty = function
  | TVar a -> a
  | Imp (a, b) -> "(" ^ string_of_ty a ^ " -> " ^ string_of_ty b ^ ")"
  | And (a, b) -> "(" ^ string_of_ty a ^ " /\\ " ^ string_of_ty b ^ ")"
  | Or (a, b) -> "(" ^ string_of_ty a ^ " \\/ " ^ string_of_ty b ^ ")"
  | True -> "T"
  | False -> "_"
  | Nat -> "nat"

let () =
  assert (string_of_ty (Imp (TVar "A", TVar "B")) = "(A -> B)");
  assert (
    string_of_ty (Imp (Imp (TVar "A", TVar "B"), Imp (TVar "A", TVar "C")))
    = "((A -> B) -> (A -> C))")

let rec string_of_tm = function
  | Var x -> x
  | App (f, x) -> "(" ^ string_of_tm f ^ " " ^ string_of_tm x ^ ")"
  | Abs (x, ty, t) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty ty ^ ") -> " ^ string_of_tm t ^ ")"
  | Pair (a, b) -> "(" ^ string_of_tm a ^ ", " ^ string_of_tm b ^ ")"
  | Fst a -> "fst(" ^ string_of_tm a ^ ")"
  | Snd a -> "snd(" ^ string_of_tm a ^ ")"
  | Unit -> "()"
  | Left (a, ty) -> "left(" ^ string_of_tm a ^ ", " ^ string_of_ty ty ^ ")"
  | Right (ty, b) -> "right(" ^ string_of_ty ty ^ ", " ^ string_of_tm b ^ ")"
  | Case (t, x, u, y, v) ->
      "(case " ^ string_of_tm t ^ " of " ^ x ^ " -> " ^ string_of_tm u ^ " | "
      ^ y ^ " -> " ^ string_of_tm v ^ ")"
  | Absurd (a, ty) -> "absurd(" ^ string_of_tm a ^ ", " ^ string_of_ty ty ^ ")"
  | Zero -> "0"
  | Succ n -> "S(" ^ string_of_tm n ^ ")"
  | Rec (n, z, s) ->
      "rec(" ^ string_of_tm n ^ ", " ^ string_of_tm z ^ ", " ^ string_of_tm s
      ^ ")"

let () =
  assert (
    string_of_tm
      (Abs
         ( "f",
           Imp (TVar "A", TVar "B"),
           Abs ("x", TVar "A", App (Var "f", Var "x")) ))
    = "(fun (f : (A -> B)) -> (fun (x : A) -> (f x)))")

type context = (var * ty) list
(** Contexts. *)

exception Type_error

let rec infer_type ctx term =
  match (ctx, term) with
  | [], Var _ -> raise Type_error
  | (y, ty_y) :: _, Var x when x = y -> ty_y
  | _ :: ctx, Var x -> infer_type ctx (Var x)
  | ctx, Abs (x, ty_x, t) -> Imp (ty_x, infer_type ((x, ty_x) :: ctx) t)
  | ctx, App (t, x) -> (
      match infer_type ctx t with
      | Imp (ty_arg, ty_res) ->
          check_type ctx x ty_arg;
          ty_res
      | _ -> raise Type_error)
  | ctx, Pair (a, b) -> And (infer_type ctx a, infer_type ctx b)
  | ctx, Fst a -> (
      match infer_type ctx a with
      | And (ty_a, _) -> ty_a
      | _ -> raise Type_error)
  | ctx, Snd a -> (
      match infer_type ctx a with
      | And (_, ty_b) -> ty_b
      | _ -> raise Type_error)
  | _, Unit -> True
  | ctx, Left (a, ty_b) -> Or (infer_type ctx a, ty_b)
  | ctx, Right (ty_a, b) -> Or (ty_a, infer_type ctx b)
  | ctx, Case (t, x, u, y, v) -> (
      match infer_type ctx t with
      | Or (ty_a, ty_b) ->
          let ty_u = infer_type ((x, ty_a) :: ctx) u in
          let ty_v = infer_type ((y, ty_b) :: ctx) v in
          if ty_u = ty_v then ty_u else raise Type_error
      | _ -> raise Type_error)
  | _, Absurd (_, ty) -> ty
  | _, Zero -> Nat
  | ctx, Succ n -> (
      match infer_type ctx n with Nat -> Nat | _ -> raise Type_error)
  | ctx, Rec (n, z, s) -> (
      match (infer_type ctx n, infer_type ctx z, infer_type ctx s) with
      | Nat, ty_z, Imp (Nat, Imp (ty_t, ty_x)) when ty_z = ty_t && ty_t = ty_x
        ->
          ty_z
      | _ -> raise Type_error)

and check_type ctx term ty =
  if not (ty = infer_type ctx term) then raise Type_error

let () =
  assert (
    infer_type []
      (Abs
         ( "f",
           Imp (TVar "A", TVar "B"),
           Abs
             ( "g",
               Imp (TVar "B", TVar "C"),
               Abs ("x", TVar "A", App (Var "g", App (Var "f", Var "x"))) ) ))
    = Imp
        ( Imp (TVar "A", TVar "B"),
          Imp (Imp (TVar "B", TVar "C"), Imp (TVar "A", TVar "C")) ));
  assert (
    try
      ignore (infer_type [] (Abs ("f", TVar "A", Var "x")));
      false
    with Type_error -> true);
  assert (
    try
      ignore
        (infer_type []
           (Abs ("f", TVar "A", Abs ("x", TVar "B", App (Var "f", Var "x")))));
      false
    with Type_error -> true);
  assert (
    try
      ignore
        (infer_type []
           (Abs
              ( "f",
                Imp (TVar "A", TVar "B"),
                Abs ("x", TVar "B", App (Var "f", Var "x")) )));
      false
    with Type_error -> true)

let () =
  check_type [] (Abs ("x", TVar "A", Var "x")) (Imp (TVar "A", TVar "A"));
  assert (
    try
      ignore
        (check_type []
           (Abs ("x", TVar "A", Var "x"))
           (Imp (TVar "B", TVar "B")));
      false
    with Type_error -> true);
  assert (
    try
      ignore (check_type [] (Var "x") (TVar "A"));
      false
    with Type_error -> true)

let () =
  (* commutativity of conjunction *)
  let and_comm =
    Abs ("x", And (TVar "A", TVar "B"), Pair (Snd (Var "x"), Fst (Var "x")))
  in
  assert (string_of_ty (infer_type [] and_comm) = "((A /\\ B) -> (B /\\ A))");

  (* truth *)
  let truth = Abs ("x", Imp (True, TVar "A"), App (Var "x", Unit)) in
  assert (string_of_ty (infer_type [] truth) = "((T -> A) -> A)");

  (* commutativity of disjunction *)
  let disjunction =
    Abs
      ( "x",
        Or (TVar "A", TVar "B"),
        Case
          ( Var "x",
            "y",
            Right (TVar "B", Var "y"),
            "z",
            Left (Var "z", TVar "A") ) )
  in
  assert (string_of_ty (infer_type [] disjunction) = "((A \\/ B) -> (B \\/ A))");

  (* absurdity *)
  let falsity =
    Abs
      ( "x",
        And (TVar "A", Imp (TVar "A", Imp (TVar "B", False))),
        App (Snd (Var "x"), Fst (Var "x")) )
  in
  assert (
    string_of_ty (infer_type [] falsity)
    = "((A /\\ (A -> (B -> _))) -> (B -> _))")

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)

let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)
