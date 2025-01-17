open Expr

exception Type_error of string

let rec _reduce_int_expr = function
  | Z -> 0
  | S n -> 1 + _reduce_int_expr n
  | _ -> raise (Type_error "Not a number")

let rec to_string = function
  | Type -> "Type"
  | Var x -> x
  | App (f, x) -> "(" ^ to_string f ^ " " ^ to_string x ^ ")"
  | Abs (x, t, e) ->
      "(fun " ^ x ^ " : " ^ to_string t ^ " -> " ^ to_string e ^ ")"
  | Pi (x, a, b) -> "((" ^ x ^ " : " ^ to_string a ^ ") -> " ^ to_string b ^ ")"
  | Nat -> "Nat"
  | Z -> "0"
  | S n -> (
      try string_of_int (_reduce_int_expr (S n))
      with Type_error _ -> "S " ^ to_string n)
  | Ind (p, z, s, n) ->
      "Ind (" ^ to_string p ^ ", " ^ to_string z ^ ", " ^ to_string s ^ ", "
      ^ to_string n ^ ")"
  | Eq (a, b) -> to_string a ^ " = " ^ to_string b
  | Refl a -> "Refl " ^ to_string a
  | J (p, r, x, x', e) ->
      "J (" ^ to_string p ^ ", " ^ to_string r ^ ", " ^ to_string x ^ ", "
      ^ to_string x' ^ ", " ^ to_string e ^ ")"

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

let _fresh_var =
  let n = ref 0 in
  fun () ->
    incr n;
    "x" ^ string_of_int !n

let rec _is_free x = function
  | Type | Nat | Z -> true
  | Var y -> x = y
  | App (t, u) | Abs (_, t, u) | Pi (_, t, u) -> _is_free x t || _is_free x u
  | S n -> _is_free x n
  | Ind (p, z, s, n) ->
      _is_free x p || _is_free x z || _is_free x s || _is_free x n
  | Eq (a, b) -> _is_free x a || _is_free x b
  | Refl a -> _is_free x a
  | J (p, r, y, y', e) ->
      _is_free x p || _is_free x r || _is_free x y || _is_free x y'
      || _is_free x e

and subst x t = function
  | Type -> Type
  | Var y when x = y -> t
  | Var y -> Var y
  | App (f, a) -> App (subst x t f, subst x t a)
  | Abs (y, ty, fy) when x = y || _is_free y t ->
      let z = _fresh_var () in
      Abs (z, subst x t (subst y (Var z) ty), subst x t (subst y (Var z) fy))
  | Abs (y, ty, f) -> Abs (y, subst x t ty, subst x t f)
  | Pi (y, ty, fy) when x = y || _is_free y t ->
      let z = _fresh_var () in
      Pi (z, subst x t (subst y (Var z) ty), subst x t (subst y (Var z) fy))
  | Pi (y, ty, f) -> Pi (y, subst x t ty, subst x t f)
  | Nat -> Nat
  | Z -> Z
  | S n -> S (subst x t n)
  | Ind (p, z, s, n) -> Ind (subst x t p, subst x t z, subst x t s, subst x t n)
  | Eq (a, b) -> Eq (subst x t a, subst x t b)
  | Refl a -> Refl (subst x t a)
  | J (p, r, y, y', e) ->
      J (subst x t p, subst x t r, subst x t y, subst x t y', subst x t e)

type context = (var * (expr * expr option)) list
(** Contexts. *)

let rec string_of_context = function
  | [] -> ""
  | (x, (t, None)) :: rem ->
      x ^ " : " ^ to_string t ^ "\n" ^ string_of_context rem
  | (x, (t, Some v)) :: rem ->
      x ^ " : " ^ to_string t ^ " = " ^ to_string v ^ "\n"
      ^ string_of_context rem

let rec _lookup x = function
  | [] -> None
  | (y, (t, v)) :: _ when x = y -> Some (t, v)
  | _ :: rem -> _lookup x rem

let rec _reduce ctx = function
  | Type -> Type
  | Var x -> ( match _lookup x ctx with Some (_, Some v) -> v | _ -> Var x)
  | App (Abs (x, _, b), a) -> subst x a b
  | App (f, a) -> App (_reduce ctx f, _reduce ctx a)
  | Abs (x, a, b) -> Abs (x, _reduce ctx a, _reduce ((x, (a, None)) :: ctx) b)
  | Pi (x, a, b) -> Pi (x, _reduce ctx a, _reduce ((x, (a, None)) :: ctx) b)
  | Nat -> Nat
  | Z -> Z
  | S n -> S (_reduce ctx n)
  | Ind (p, z, s, n) -> (
      let p' = _reduce ctx p and z' = _reduce ctx z and s' = _reduce ctx s in
      match _reduce ctx n with
      | Z -> z'
      | S n' -> _reduce ctx (App (App (s', n'), Ind (p', z', s', n')))
      | n' -> Ind (p', z', s', n'))
  | Eq (a, b) -> Eq (_reduce ctx a, _reduce ctx b)
  | Refl a -> Refl (_reduce ctx a)
  | J (_, r, x, x', Refl y) when x = x' && x' = y -> App (r, x)
  | J (p, r, x, x', e) ->
      J
        ( _reduce ctx p,
          _reduce ctx r,
          _reduce ctx x,
          _reduce ctx x',
          _reduce ctx e )

let rec normalize ctx t =
  let t' = _reduce ctx t in
  if t = t' then t else normalize ctx t'

let rec _alpha t u =
  match (t, u) with
  | Type, Type -> true
  | Var x, Var y -> x = y
  | App (f, a), App (g, b) -> _alpha f g && _alpha a b
  | (Abs (x, a, b), Abs (y, c, d) | Pi (x, a, b), Pi (y, c, d)) when x = y ->
      _alpha a c && _alpha b d
  | Abs (x, a, b), Abs (y, c, d) | Pi (x, a, b), Pi (y, c, d) ->
      _alpha a (subst y (Var x) c) && _alpha b (subst y (Var x) d)
  | Nat, Nat | Z, Z -> true
  | S a, S b -> _alpha a b
  | Ind (p, z, s, n), Ind (p', z', s', n') ->
      _alpha p p' && _alpha z z' && _alpha s s' && _alpha n n'
  | Eq (a, a'), Eq (b, b') -> _alpha a b && _alpha a' b'
  | Refl a, Refl b -> _alpha a b
  | J (p, r, x, x', e), J (p', r', y, y', e') ->
      _alpha p p' && _alpha r r' && _alpha x y && _alpha x' y' && _alpha e e'
  | _ -> false

let conv ctx t u = _alpha (normalize ctx t) (normalize ctx u)

let rec infer ctx = function
  | Type | Pi _ | Nat -> Type
  | Var x -> (
      match _lookup x ctx with
      | Some (t, _) -> t
      | _ -> raise (Type_error "Variable not found"))
  | App (f, x) -> (
      match infer ctx f with
      | Pi (y, a, b) when conv ctx a (infer ctx x) -> subst y x b
      | Pi _ -> raise (Type_error "Application type mismatch")
      | _ -> raise (Type_error "Application of non-function"))
  | Abs (x, tx, fx) ->
      let tf = infer ((x, (tx, None)) :: ctx) fx in
      Pi (x, tx, tf)
  | Z -> Nat
  | S n -> (
      match infer ctx n with
      | Nat -> Nat
      | _ -> raise (Type_error "S expects a number"))
  | Ind (p, z, s, n) -> (
      if not (conv ctx (infer ctx z) (App (p, Z))) then (
        print_endline (to_string (infer ctx z));
        print_endline (to_string (App (p, Z)));
        raise (Type_error "Induction base value and predicate type mismatch"));
      if not (conv ctx (infer ctx n) Nat) then
        raise (Type_error "Induction step value is not a number");
      match infer ctx s with
      | Pi (m, Nat, Pi (_, q, r))
        when conv ((m, (Nat, None)) :: ctx) (App (p, Var m)) q
             && conv ((m, (Nat, None)) :: ctx) (App (p, S (Var m))) r ->
          normalize ctx (App (p, n))
      | _ -> raise (Type_error "Induction step type mismatch"))
  | Eq (a, b) when conv ctx (infer ctx a) (infer ctx b) -> Type
  | Refl a ->
      let t = infer ctx a in
      Eq (t, t)
  | _ -> assert false

let check ctx t a =
  if conv ctx (infer ctx t) a then () else raise (Type_error "Type mismatch")
