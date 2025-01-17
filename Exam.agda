--- Fill in your name here:

---
--- Equality
---

infix 4 _≡_

-- definition of equality
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- equality is symmetric
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- equality is transitive
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

-- equality is a congruence
cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

-- equality is substitutive
subst : {A : Set} (P : A → Set) → {x y : A} → x ≡ y → P x → P y
subst P refl p = p

---
--- Truth
---

-- truth
data ⊤ : Set where
  tt : ⊤

---
--- Falsity
---

-- falsity
data ⊥ : Set where

-- ex falso quot libet
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- negation
¬_ : (A : Set) → Set
¬ A = A → ⊥

---
--- Product / conjunction
---

infixr 2 _×_
infixr 2 _∧_
infixr 4 _,_

-- product
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

-- conjunction
_∧_ = _×_

---
--- Dependent product
---

-- dependent product
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

-- existential quantification
∃ = Σ

---
--- Disjunction
---

infixr 1 _∨_

-- disjunction
data _∨_ (A B : Set) : Set where
  left  : (x : A) → A ∨ B
  right : (y : B) → A ∨ B

-- decidable types
Dec : (A : Set) → Set
Dec A = A ∨ ¬ A

---
--- Booleans
---

-- booleans
data Bool : Set where
  true : Bool
  false : Bool

-- negation
not : Bool → Bool
not true = false
not false = true

-- negation is involutive
not-not : (b : Bool) → not (not b) ≡ b
not-not true  = refl
not-not false = refl

---
--- Natural numbers
---

-- natural numbers
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- 0 is different from 1
0≢1 : ¬ (0 ≡ 1)
0≢1 ()

infix 6 _+_

-- addition
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

infix 7 _*_

-- multiplication
_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

infix 4 _≤_

-- order on natural numbers
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}                 → zero  ≤ n
  s≤s : {m n : ℕ} (m≤n : m ≤ n) → suc m ≤ suc n

-- order is reflexive
≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

-- order is transitive
≤-trans : {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n l' = z≤n
≤-trans (s≤s l) (s≤s l') = s≤s (≤-trans l l')

infix 4 _<_

-- strict order on natural numbers
_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

infix 4 _>_

-- reversed strict orer on natural numbers
_>_ : ℕ → ℕ → Set
m > n = n < m

---
--- Lists
---

infixr 5 _∷_

-- lists
data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (l : List A) → List A

-- singleton list
[_] : {A : Set} → A → List A
[ x ] = x ∷ []

infixr 5 _++_

-- concatenation
_++_ : {A : Set} → List A → List A → List A
[] ++ m      = m
(x ∷ l) ++ m = x ∷ (l ++ m)

-- length
length : {A : Set} → List A → ℕ
length []      = 0
length (x ∷ l) = suc (length l)


---cut here---✂---✂---✂---✂---✂---✂---✂---✂---✂---✂---✂---✂---✂---✂---cut here--


---
--- Put your answers below this line.
--- (and don't edit the above)
---


---
--- Propositional logic
---

pl1 : {A B : Set} → ((A → B) ∨ B) → A → B
pl1 (left f) a = f a
pl1 (right b) _ = b

pl2 : {A B C : Set} → A ∧ B → (B → C) → C ∧ A
pl2 (a , b) f = f b , a

pl3 : {A : Set} → ¬ ¬ ¬ A → ¬ A
pl3 x a = x (λ nota → nota a)

pl4 : {A B : Set} → A ∧ B → A ∨ B
pl4 (a , b) = left a

pl5 : {A B C : Set} → A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C)
pl5 (left a) = left a , left a
pl5 (right (b , c)) = right b , right c

lem : Set₁
lem = (A : Set) → ¬ A ∨ A

material : Set₁
material = (A B : Set) → (A → B) → ¬ A ∨ B

material→lem : material → lem
material→lem mat A = mat A A (λ z → z)

∨-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
∨-elim (left a) f _ = f a
∨-elim (right b) _ g = g b

lem→material : lem → material
lem→material le A B f = ∨-elim(le A) left (λ a → right (f a))

fo : {A : Set} {B : A → Set} → ((x : A) → ¬ (B x)) → ¬ (∃ A B)
fo f (a , Ba) = f a Ba

postulate
  A    : Set
  _>>_ : A → A → Set
  irr  : (x : A) → ¬ (x >> x)

is-a-boss : A → Set
is-a-boss a = ∃ A (λ b → a >> b)

boss-of-bosses : (a : A) → is-a-boss a → ((b : A) → is-a-boss b → a >> b) → ⊥
boss-of-bosses a aboss f = (irr a) (f a aboss)

---
--- Maximum
---

max : ℕ → ℕ → ℕ
max zero b = b
max a zero = a
max (suc a) (suc b) = suc (max a b)

test-max1 : max 3 5 ≡ 5
test-max1 = refl

test-max2 : max 5 3 ≡ 5
test-max2 = refl

max-idem : (x : ℕ) → max x x ≡ x
max-idem zero = refl
max-idem (suc x) = cong suc (max-idem x)

max-assoc : (x y z : ℕ) → max (max x y) z ≡ max x (max y z)
max-assoc zero y z = refl
max-assoc (suc x) zero z = refl
max-assoc (suc x) (suc y) zero = refl
max-assoc (suc x) (suc y) (suc z) = cong suc (max-assoc x y z)

max-sym : (x y : ℕ) → max x y ≡ max y x
max-sym zero zero = refl
max-sym zero (suc y) = refl
max-sym (suc x) zero = refl
max-sym (suc x) (suc y) = cong suc (max-sym x y)

max-≤-l : (x y : ℕ) → x ≤ max x y
max-≤-l zero y = z≤n
max-≤-l (suc x) zero = ≤-refl (suc x)
max-≤-l (suc x) (suc y) = s≤s (max-≤-l x y)

max-sup : (x y m : ℕ) → x ≤ m → y ≤ m → max x y ≤ m
max-sup zero y m _ y≤m = y≤m
max-sup (suc x) zero m x≤m _ = x≤m
max-sup (suc x) (suc y) (suc m) (s≤s a) (s≤s b) = s≤s (max-sup x y m a b)

---
--- Strict order
---

<-irrefl : {n : ℕ} → ¬ (n < n)
<-irrefl (s≤s n<n) = <-irrefl n<n

<-neq : {m n : ℕ} → m < n → ¬ (m ≡ n)
<-neq {zero} {suc n} m<n ()
<-neq {suc m} {suc _} (s≤s sucm≤m) refl = <-neq sucm≤m refl

<-trans : {m n o : ℕ} → m < n → n < o → m < o
<-trans (s≤s z≤n) (s≤s _) = s≤s z≤n
<-trans (s≤s (s≤s m≤n)) (s≤s r) = s≤s (<-trans (s≤s m≤n) r)

<-antisym : {m n : ℕ} → m < n → m > n → ⊥
<-antisym m<n m>n = <-irrefl (<-trans m<n m>n)

---
--- Subtraction
---

_-_ : ℕ → ℕ → ℕ
a - zero = a
zero - suc b = zero
suc a - suc b = a - b

infix 6 _-_

add-sub-lm1 : (n m : ℕ) → (m + suc n) ≡ suc (m + n)
add-sub-lm1 zero zero = refl
add-sub-lm1 zero (suc m) = cong suc (add-sub-lm1 zero m)
add-sub-lm1 (suc n) zero = refl
add-sub-lm1 (suc n) (suc m) = cong suc (add-sub-lm1 (suc n) m)

add-sub-lm2 : (m n : ℕ) → ((suc m) - n) ≡ suc (m - n)
add-sub-lm2 m zero = refl
add-sub-lm2 zero (suc n) = {!   !} -- grrr
add-sub-lm2 (suc m) (suc n) = add-sub-lm2 m n

add-sub : (m n : ℕ) → (m + n) - n ≡ m
add-sub zero zero = refl
add-sub zero (suc n) = add-sub zero n
add-sub (suc m) zero = cong suc (add-sub m zero)
add-sub (suc m) (suc n) = {!   !}

sub-add : (m n : ℕ) → n ≤ m → (m - n) + n ≡ m
sub-add = {!   !}

---
--- Even numbers
---

data even : ℕ → Set where
  even-zero : even zero
  even-ss   : (n : ℕ) → even n → even (suc (suc n))

even10 : even 10
even10 = even-ss 8 (even-ss 6 (even-ss 4 (even-ss 2 (even-ss zero even-zero))))

neven9 : ¬ (even 9)
neven9 (even-ss .7 (even-ss .5 (even-ss .3 (even-ss .1 ()))))

is-even : ℕ → Bool
is-even zero = true
is-even (suc zero) = false
is-even (suc (suc n)) = is-even n

is-even-correct : (n : ℕ) → is-even n ≡ true → even n
is-even-correct zero _ = even-zero
is-even-correct (suc (suc n)) p = even-ss n (is-even-correct n p)

even200 : even 200
even200 = is-even-correct 200 refl

is-even-correct' : (n : ℕ) → is-even n ≡ false → ¬ (even n)
is-even-correct' (suc _) isnotevenn (even-ss n evenn) = is-even-correct' n isnotevenn evenn

neven479 : ¬ (even 479)
neven479 x = is-even-correct' 479 refl x

even-suc : (n : ℕ) → even n → ¬ (even (suc n))
even-suc (suc (suc n)) (even-ss _ evenn) (even-ss _ evensucn) = even-suc n evenn evensucn

even-suc' : (n : ℕ) → ¬ (even n) → even (suc n)
even-suc' zero x = ⊥-elim (x even-zero)
even-suc' (suc zero) x = even-ss zero even-zero
even-suc' (suc (suc n)) x = even-ss (suc n) (even-suc' n (λ z → x (even-ss n z)))

even-pred : (n : ℕ) → even (suc (suc n)) → even n
even-pred zero b = even-zero
even-pred (suc zero) (even-ss .1 b) = b
even-pred (suc (suc n)) (even-ss .(suc (suc n)) b) = b

even-dec : (n : ℕ) → Dec (even n)
even-dec zero = left even-zero
even-dec (suc zero) = right (λ ())
even-dec (suc (suc n)) with even-dec n
... | left e = left (even-ss n e)
... | right eto⊥ = right (λ essn → eto⊥ (even-pred n essn))

---
--- Filtering
---

nonzero : ℕ → Set
nonzero zero    = ⊥
nonzero (suc n) = ⊤

True : {A : Set} → A → Set
True _ = ⊤

every : {A : Set} (P : A → Set) → List A → Set
every P [] = ⊤
-- every P (x ∷ []) = P x
every P (x ∷ l) = P x × every P l

-- NOTE: This doesn't work grrrr
-- every P (x ∷ l) with P x
-- ... | ⊤ = every P l
-- ... ∣ ⊥ = ⊥

nz1 : every nonzero []
nz1 = tt

nz2 : every nonzero (1 ∷ 2 ∷ 3 ∷ [])
nz2 = tt , tt , tt , tt

nz3 : ¬ (every nonzero (1 ∷ 0 ∷ 3 ∷ []))
nz3 (tt , () , x₁)

every-True : {A : Set} (l : List A) → every True l
every-True [] = tt
every-True (x ∷ l) = tt , every-True l

DecP : {A : Set} (P : A → Set) → Set
DecP {A} P = (x : A) → Dec (P x)

True-dec : {A : Set} → DecP (True {A})
True-dec _ = left tt

nonzero-dec : DecP nonzero
nonzero-dec zero = right (λ x → x)
nonzero-dec (suc x) = left tt

filter : {A : Set} {P : A → Set} → DecP P → List A → List A
filter decp [] = []
filter decp (x ∷ l) with decp x
... | left _ = x ∷ (filter decp l)
... | right _ = filter decp l

fnz : filter nonzero-dec (1 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 3 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
fnz = refl

filter-true : {A : Set} (l : List A) → filter True-dec l ≡ l
filter-true [] = refl
filter-true (x ∷ l) = cong (λ l' → x ∷ l') (filter-true l)

filter-every : {A : Set} {P : A → Set} (dec : DecP P) (l : List A) → every P (filter dec l)
filter-every dec [] = tt
filter-every dec (x ∷ l) with dec x
... | left y = y , filter-every dec l
... | right y = filter-every dec l

-- dirty... I feel like this is already known
n≤n+1 : (n : ℕ) → n ≤ suc n
n≤n+1 zero = z≤n
n≤n+1 (suc n) = s≤s (n≤n+1 n)

filter-length : {A : Set} {P : A → Set} (dec : DecP P) (l : List A) → length (filter dec l) ≤ length l
filter-length dec [] = z≤n
filter-length dec (x ∷ l) with dec x
... | left y = s≤s (filter-length dec l)
... | right y = ≤-trans (filter-length dec l) (n≤n+1 (length l))

¬' : {A : Set} (P : A → Set) → (A → Set)
¬' P x = ¬ (P x)

¬DecP : {A : Set} {P : A → Set} → DecP P → DecP (¬' P)
¬DecP decp x with decp x
... | left y = right (λ z → z y)
... | right y = left y

length-both : {A : Set} {P : A → Set} (dec : DecP P) (l : List A) → length (filter dec l) + length (filter (¬DecP dec) l) ≡ length l
length-both dec [] = refl
length-both dec (x ∷ l) with dec x
... | left y = cong suc (length-both dec l)
... | right y = trans {!   !} {!   !}

---
--- Search trees
---

data mem {A : Set} : (x : A) (l : List A) → Set where
  mem-hd : {x : A} {l : List A} → mem x (x ∷ l)
  mem-tl : {x y : A} {l : List A} → mem x l → mem x (y ∷ l)

test-mem1 : mem 2 (1 ∷ 2 ∷ 3 ∷ [])
test-mem1 = mem-tl mem-hd

test-mem2 : ¬ (mem 5 (1 ∷ 2 ∷ 3 ∷ []))
test-mem2 (mem-tl (mem-tl (mem-tl ())))

data Tree : Set where
  Node : Tree →  ℕ → Tree → Tree
  Leaf : ℕ → Tree

T : Tree
T = Node (Leaf 1) 3 (Node (Leaf 2) 5 (Leaf 4))

data tree-mem (n : ℕ) : Tree → Set where
  tree-mem-nd : (t u : Tree) → tree-mem n (Node t n u)
  tree-mem-l  : (t : Tree) → tree-mem n t → (x : ℕ) → (u : Tree) → tree-mem n (Node t x u)
  tree-mem-r  : (t : Tree) → (x : ℕ) → (u : Tree) → tree-mem n u → tree-mem n (Node t x u)
  tree-mem-lf : tree-mem n (Leaf n)

test-tm1 : tree-mem 5 T
test-tm1 = tree-mem-r (Leaf 1) 3 (Node (Leaf 2) 5 (Leaf 4)) (tree-mem-nd (Leaf 2) (Leaf 4))

test-tm2 : ¬ (tree-mem 9 T)
test-tm2 (tree-mem-r .(Leaf 1) .3 .(Node (Leaf 2) 5 (Leaf 4)) (tree-mem-l .(Leaf 2) () .5 .(Leaf 4)))
test-tm2 (tree-mem-r .(Leaf 1) .3 .(Node (Leaf 2) 5 (Leaf 4)) (tree-mem-r .(Leaf 2) .5 .(Leaf 4) ()))

elements : Tree → List ℕ
elements (Node l x r) = elements l ++ x ∷ [] ++ elements r
elements (Leaf x) = x ∷ []

test-el : elements T ≡ 1 ∷ 3 ∷ 2 ∷ 5 ∷ 4 ∷ []
test-el = refl

mem++l : {A : Set} (x : A) (k l : List A) → mem x k → mem x (k ++ l)
mem++l x (x₁ ∷ k) [] memxk = {!   !}
mem++l x (x₁ ∷ k) (y ∷ l) memxk = {!   !}

mem++r : {A : Set} (x : A) (k l : List A) → mem x l → mem x (k ++ l)
mem++r = {!   !}

mem→elements : (n : ℕ) (t : Tree) → tree-mem n t → mem n (elements t)
mem→elements n (Node t x t₁) tmemnt = {!   !}
mem→elements n (Leaf x) tmemnt = {!   !}
