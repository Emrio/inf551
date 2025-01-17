open import Data.Product

-- ×-comm : (A B : Set) → (A × B) → (B × A)
×-comm : {A B : Set} → (A × B) → (B × A)
×-comm (fst , snd) = snd , fst

id : {A : Set} → A → A
id a = a

K : {A B : Set} → A → B → A
K a b = a

app : {A B : Set} → (A → B) → A → B
app p a = p a

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

comp : {A B C : Set} → (A → B) → (B → C) → (A → C)
comp a b c = b (a c)

S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S x y z = x z (y z)

open import Data.Product renaming (_×_ to _∧_)

proj1 : {A B : Set} → (A ∧ B) → A
proj1 (a , b) = a

proj2 : {A B : Set} → (A ∧ B) → B
proj2 (a , b) = b

diag : {A : Set} → A → (A ∧ A)
diag a = a , a

comm : {A B : Set} → (A ∧ B) → (B ∧ A)
comm (a , b) = (b , a)

curry1 : {A B C : Set} → (A ∧ B → C) → (A → B → C)
curry1 f a b = f (a , b)

curry2 : {A B C : Set} → (A → B → C) → (A ∧ B → C)
curry2 f (a , b) = f a b

equiv : (A B : Set) → Set
equiv A B = (A → B) ∧ (B → A)

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) ∧ (B → A)

currying : {A B C : Set} → (A ∧ B → C) ↔ (A → B → C)
currying = curry1 , curry2

distrib : {A B C : Set} → (A → (B ∧ C)) ↔ ((A → B) ∧ (A → C))
distrib = (λ f → (λ a → proj1 (f a)) , λ b → proj2 (f b)) , λ x a → proj1 x a , proj2 x a

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

or-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
or-elim (left a∨b) l r = l a∨b
or-elim (right a∨b) l r = r a∨b

or-comm : {A B C : Set} → (A ∨ B) → (B ∨ A)
or-comm (left x) = right x
or-comm (right x) = left x

dist : {A B C : Set} → (A ∧ (B ∨ C)) → (A ∧ B) ∨ (A ∧ C)
dist (a , left x) = left (a , x)
dist (a , right x) = right (a , x)

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim = λ ()

¬ : Set → Set
¬ a = a → ⊥

contr : {A B : Set} → (A → B) → (¬ B → ¬ A)
contr f notb a = notb (f a)

non-contr : {A : Set} → ¬ (A ∧ ¬ A)
non-contr (a , nota) = nota a

nni : {A : Set} → A → ¬ (¬ A)
nni a nota = nota a

⊥-nne : ¬ (¬ ⊥) → ⊥
⊥-nne z = z (λ z₁ → z₁)

¬-elim : {A B : Set} → ¬ A → A → B
¬-elim nota a = ⊥-elim (nota a)

dm∧ : {A B : Set} → ¬ A ∧ ¬ B → ¬ (A ∨ B)
dm∧ (nota , notb) (left a) = nota a
dm∧ (nota , notb) (right b) = notb b

dm∨ : {A B : Set} → ¬ A ∨ ¬ B → ¬ (A ∧ B)
dm∨ (left nota) (a , b) = nota a
dm∨ (right notb) (a , b) = notb b

nnlem : {A : Set} → ¬ (¬ (A ∨ (¬ A)))
nnlem e = e (right (λ x → e (left x)))

rp : {A : Set} → (A → ¬ A) → ((¬ A) → A) → ⊥
rp z z₁ = z (z₁ (λ z₂ → z z₂ z₂)) (z₁ (λ z₂ → z z₂ z₂))

⊤ = ¬ ⊥

ti : {A : Set} → (⊤ → A) → A
ti z = z id

dmnt : ¬ ⊤ → ⊥
dmnt z = z id

dmtn : ⊥ → ¬ ⊤
dmtn x y = y x

lem : Set₁
lem = (A : Set) → A ∨ (¬ A)

nne : Set₁
nne = (A : Set) → ¬ (¬ A) → A

nne-lem : nne → lem
nne-lem x A = x (A ∨ ((x : A) → ⊥)) (λ z → z (right (λ x → z (left x))))

lem-nne' : (A : Set) → (A ∨ ¬ A) → ¬ (¬ A) → A
lem-nne' A (left a) norna = a
lem-nne' A (right na) norna = ⊥-elim (norna na)

lem-nne : lem → nne
lem-nne = λ lem A nna → lem-nne' A (lem A) nna

pierce : Set₁
pierce = {A B : Set} → ((A → B) → A) → A

pierce-lem : pierce → lem
pierce-lem x A = x (λ z → right (λ x → z (left x)))

-- lem-pierce : lem → pierce
-- lem-pierce lem A = {!   !}

postulate U : Set

∀-comm : {P : U → U → Set} → ((x : U) → (y : U) → P x y) → ((y : U) → (x : U) → P x y)
∀-comm f y x = f x y

∃-comm : {P : U → U → Set} → ∃ (λ x → ∃ (λ y → P x y)) → ∃ (λ y → ∃ (λ x → P x y))
∃-comm (x , (y , p)) = y , (x , p)

-- switch-∀-∃ : {P : U → U → Set} → ∃ (λ x → (y : U) → P x y) → ((y : U) → ∃ (λ x -> P x y))
-- switch-∀-∃ (fst , (a , b)) y = y , {!   !}
