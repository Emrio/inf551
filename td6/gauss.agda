open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Div2
open ≡-Reasoning

+-com : (m n : ℕ) → m + n ≡ n + m
+-com zero    n = sym (+-identityʳ n)
+-com (suc m) n = begin
  suc m + n   ≡⟨ refl ⟩
  suc (m + n) ≡⟨ {!   !} ⟩
  n + suc m   ∎

div2-double : (n : ℕ) → div2 (2 * n) ≡ n
div2-double 0 = refl
div2-double 1 = refl
div2-double (suc (suc n)) = begin
  div2 (2 * (2 + n)) ≡⟨ refl ⟩
  suc (div2 (n + suc (suc (n + 0)))) ≡⟨ cong (λ m → suc (div2 m)) (+-suc n (suc (n + 0))) ⟩
  suc (div2 (suc (n + (suc (n + 0)))))≡⟨ cong (λ m → suc (div2 (suc m))) (+-suc n (n + 0)) ⟩
  suc (div2 (suc (suc (2 * n))))≡⟨ cong (λ m → suc (suc m)) (div2-double n) ⟩
  suc (suc n) ∎

triangular : ℕ → ℕ
triangular 0 = 0
triangular (suc n) = triangular n + suc n
