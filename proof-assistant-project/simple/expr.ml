type tvar = string
(** Type variables. *)

type var = string
(** Term variables. *)

(** Types. *)
type ty =
  | TVar of tvar
  | Imp of ty * ty
  | And of ty * ty
  | Or of ty * ty
  | True
  | False
  | Nat

(** Terms. *)
type tm =
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Unit
  | Left of tm * ty
  | Right of ty * tm
  | Case of tm * var * tm * var * tm
  | Absurd of tm * ty
  | Zero
  | Succ of tm
  | Rec of tm * tm * tm
