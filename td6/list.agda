open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

length : {A : Set} → List A → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)

concat : {A : Set} → List A → List A → List A
concat []       ylst = ylst
concat (x ∷ xs) ylst = x ∷ (concat xs ylst)

concat-length : {A : Set} → (l l' : List A) → length (concat l l') ≡ length l + length l'
concat-length []       l' = refl
concat-length (x ∷ xs) l' = cong suc (concat-length xs l')

concat-assoc : {A : Set} → (l l' l'' : List A) → concat l (concat l' l'') ≡ concat (concat l l') l''
concat-assoc []       l' l'' = refl
concat-assoc (x ∷ xs) l' l'' = cong (λ l → x ∷ l) (concat-assoc xs l' l'')

-- # List.rev [1;4;5;7];;
-- - : int list = [7; 5; 4; 1]

snoc : {A : Set} → List A → A → List A
snoc []       x = x ∷ []
snoc (y ∷ ys) x = y ∷ (snoc ys x)

rev : {A : Set} → List A → List A
rev []       = []
rev (x ∷ xs) = snoc (rev xs) x

rev-snoc-rev : {A : Set} → (l : List A) → (x : A) → x ∷ rev l ≡ rev (snoc l x)
rev-snoc-rev []      x = refl
rev-snoc-rev (y ∷ l) x = trans (cong (λ l → snoc l y) (rev-snoc-rev l x)) refl

rev-rev : {A : Set} → (l : List A) → l ≡ rev (rev l)
rev-rev []       = refl
rev-rev (x ∷ xs) = trans (cong (λ l → x ∷ l) (rev-rev xs)) (rev-snoc-rev (rev xs) x)

-- ('a -> bool) -> 'a list -> 'a list
-- # List.filter (fun n -> n mod 2 = 0) [1;3;4;6;7;10;11;12];;
-- - : int list = [4; 6; 10; 12]

filter : {A : Set} → (p : A → Bool) → (l : List A) → List A
filter p []       = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false = filter p xs

filter-false : {A : Set} → (l : List A) → filter (λ x → false) l ≡ []
filter-false []       = refl
filter-false (x ∷ xs) = filter-false xs

filter-true : {A : Set} → (l : List A) → filter (λ x → true) l ≡ l
filter-true []       = refl
filter-true (x ∷ xs) = cong (λ l → x ∷ l) (filter-true xs)
