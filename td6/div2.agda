module Div2 where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties using (+-suc)
open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

div2 : ℕ → ℕ
div2 zero = zero
div2 (suc zero) = zero
div2 (suc (suc n)) = suc (div2 n)

test5 : ℕ
test5 = div2 (suc (suc (suc (suc (suc zero)))))

div2' : (n : ℕ) → Σ ℕ (λ q → (2 * q ≡ n) ∨ (suc (2 * q) ≡ n))
div2' zero = zero , left refl
div2' (suc zero) = zero , right refl
div2' (suc (suc n)) with div2' n
... | q , left e = suc q , left (trans (cong suc (+-suc q (q + 0))) (cong (λ x → suc (suc x)) e))
... | q , right o = suc q , right (cong (λ x → suc (suc x)) (trans (+-suc q (q + 0)) o))
