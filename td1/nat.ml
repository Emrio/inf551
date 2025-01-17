type nat = Z | S of nat

let rec add_nat a = function Z -> a | S y -> add_nat (S a) y

let rec is_even = function Z -> true | S Z -> false | S (S y) -> is_even y

let pred = function Z -> None | S y -> Some y

let rec half = function Z -> Z | S Z -> Z | S (S y) -> S (half y)

let rec half_alt = function
  | Z -> Some Z
  | S Z -> None
  | S (S y) -> ( match half_alt y with None -> None | Some y -> Some (S y))
