-- open import Data.List
open import Data.Nat
open import Data.Nat.Properties using (+-assoc)
open import Data.Product hiding (zip)
open import Relation.Binary.PropositionalEquality

-- hd : {A : Set} → List A → A
-- hd []       = ?
-- hd (x ∷ xs) = x

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

vec-hd : {A : Set} {n : ℕ} → Vec A (suc n) → A
vec-hd (x ∷ xs) = x

vec-tl : {A : Set} {n : ℕ} → Vec A (suc n) → A
vec-tl (x ∷ []) = x
vec-tl (x ∷ (y ∷ ys)) = vec-tl (x ∷ ys)

vec-concat : {A : Set} {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
vec-concat []       ys = ys
vec-concat (x ∷ xs) ys = x ∷ vec-concat xs ys

vec-push-back : {A : Set} {n : ℕ} → Vec A n → A → Vec A (suc n)
vec-push-back []       x = x ∷ []
vec-push-back (y ∷ ys) x = y ∷ vec-push-back ys x

vec-rev : {A : Set} {n : ℕ} → Vec A n → Vec A n
vec-rev []       = []
vec-rev (x ∷ xs) = vec-push-back (vec-rev xs) x

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

vec-ith : {A : Set} {n : ℕ} → Vec A n → Fin n → A
vec-ith (x ∷ xs) zero    = x
vec-ith (x ∷ xs) (suc i) = vec-ith xs i

vec-zip : {A B : Set} {n : ℕ} → Vec A n → Vec B n → Vec (A × B) n
vec-zip []       []       = []
vec-zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ vec-zip xs ys

coe : {A B : Set} → A ≡ B → A → B
coe refl x = x

-- TODO: concat-assoc
