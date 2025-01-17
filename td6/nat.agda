open import Relation.Nullary
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

data _≡_ {A : Set} (x : A) : (y : A) → Set where
  refl : x ≡ x

infix 4 _≡_

suc-≡ : {m n : ℕ} → (m ≡ n) → suc m ≡ suc n
suc-≡ refl = refl

+-unit-l : {n : ℕ} → zero + n ≡ n
+-unit-l = refl

+-unit-r : (n : ℕ) → n + zero ≡ n
+-unit-r zero = refl
+-unit-r (suc n) = suc-≡ (+-unit-r n)

+-assoc : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = suc-≡ (+-assoc m n p)

+-suc : (m n : ℕ) → suc (m + n) ≡ m + suc n
+-suc zero n = refl
+-suc (suc m) n = suc-≡ (+-suc m n)

suc-nzero : (n : ℕ) → ¬ (suc n ≡ zero)
suc-nzero x ()

rec : (P : ℕ → Set) → P zero → ({n : ℕ} → P n → P (suc n)) → (m : ℕ) → P m
rec P P0 Pnn+1 zero = P0
rec P P0 Pnn+1 (suc m) = Pnn+1 (rec P P0 Pnn+1 m)

+-unit-r2 : (n : ℕ) → n + zero ≡ n
+-unit-r2 n = rec (λ m → m + zero ≡ m) refl (λ m → suc-≡ m) n

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl n = n

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

suc-≡-cong : {m n : ℕ} → m ≡ n → suc m ≡ suc n
suc-≡-cong = cong suc

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-unit-r n)
+-comm (suc m) n = trans (suc-≡ (+-comm m n)) (+-suc n m)

suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

nat-dec : (m n : ℕ) → (m ≡ n) ∨ ¬ (m ≡ n)
nat-dec zero zero = left refl
nat-dec zero (suc n) = right λ ()
nat-dec (suc m) zero = right λ ()
nat-dec (suc m) (suc n) with nat-dec m n
... | left p = left (suc-≡ p)
... | right ¬p = right λ x → ¬p (suc-inj x)

J : (A : Set) → (P : (x : A) → (y : A) → (p : x ≡ y) → Set) → (r : (x : A) → P x x refl) → (x : A) → (y : A) → (p : x ≡ y) → P x y p
J A P r x y refl = r x

-- TODO: *-comm
