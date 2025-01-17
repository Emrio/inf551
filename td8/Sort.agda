open import Relation.Binary.PropositionalEquality
open import Data.Bool using (Bool ; true ; false)
open import Data.Unit using (⊤ ; tt)
open import Data.Product renaming (_×_ to _∧_ ; proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Data.List hiding (length ; head ; merge)

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}                 → zero  ≤ n
  s≤s : {m n : ℕ} (m≤n : m ≤ n) → suc m ≤ suc n

≤-pred : {m n : ℕ} → (suc m ≤ suc n) → m ≤ n
≤-pred (s≤s x) = x

≤-suc : {m n : ℕ} → m ≤ n → suc m ≤ suc n
≤-suc z≤n = s≤s z≤n
≤-suc (s≤s x) = s≤s (s≤s x)

≤s : (n : ℕ) → n ≤ suc n
≤s zero = z≤n
≤s (suc n) = s≤s (≤s n)

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : {m n p : ℕ} → (m ≤ n) → (n ≤ p) → (m ≤ p)
≤-trans z≤n n≤p = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

_≤?_ : (m n : ℕ) → (m ≤ n) ∨ (n ≤ m)
zero ≤? n = left z≤n
suc m ≤? zero = right z≤n
suc m ≤? suc n with m ≤? n
suc m ≤? suc n | left e = left (s≤s e)
suc m ≤? suc n | right e = right (s≤s e)

insert : (x : ℕ) → (l : List ℕ) → List ℕ
insert x [] = x ∷ []
insert x (y ∷ l) with x ≤? y
insert x (y ∷ l) | left e = x ∷ (y ∷ l)
insert x (y ∷ l) | right e = y ∷ (insert x l)

sort : List ℕ → List ℕ
sort [] = []
sort (x ∷ l) = insert x (sort l)

test : List ℕ
test = sort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

data _≤*_ : ℕ → List ℕ → Set where
  n≤*[] : {n : ℕ} → n ≤* []
  n≤*l  : {n m : ℕ} → {l : List ℕ} → (n ≤ m) → (n ≤* l) → n ≤* (m ∷ l)

data sorted : List ℕ → Set where
  s[] : sorted []
  sl  : {x : ℕ} → {l : List ℕ} → (x ≤* l) → sorted l → sorted (x ∷ l)

≤*-trans : {x y : ℕ} → {l : List ℕ} → x ≤ y → y ≤* l → x ≤* l
≤*-trans x≤y n≤*[] = n≤*[]
≤*-trans x≤y (n≤*l z y≤*l) = n≤*l (≤-trans x≤y z) (≤*-trans x≤y y≤*l)

≤*-sorting : {x y : ℕ} → {l : List ℕ} → x ≤ y → x ≤* l → x ≤* (insert y l)
≤*-sorting x≤y n≤*[] = n≤*l x≤y n≤*[]
≤*-sorting {x} {y} {z ∷ l} x≤y (n≤*l x≤z x≤*l) with y ≤? z
... | left e = n≤*l x≤y (n≤*l x≤z x≤*l)
... | right e = n≤*l x≤z (≤*-sorting x≤y x≤*l)

insert-sorting : (x : ℕ) → (l : List ℕ) → sorted l → sorted (insert x l)
insert-sorting x [] sl=[] = sl n≤*[] sl=[]
insert-sorting x (y ∷ l) (sl z sortedl) with x ≤? y
... | left e = sl (n≤*l e (≤*-trans e z)) (sl z sortedl)
... | right e = sl (≤*-sorting e  z) (insert-sorting x l sortedl)

sort-sorting : (l : List ℕ) → sorted (sort l)
sort-sorting [] = s[]
sort-sorting (x ∷ l) = insert-sorting x (sort l) (sort-sorting l)

f : List ℕ → List ℕ
f l = []

f-sorting : (l : List ℕ) → sorted (f l)
f-sorting l = s[]

mutual
  even : ℕ → Bool
  even zero = true
  even (suc n) = odd n

  odd : ℕ → Bool
  odd zero = false
  odd (suc n) = even n

mutual
  data Sorted : Set where
    nil  : Sorted
    cons : (x : ℕ) → (l : Sorted) → (x ≤ (head x l)) → Sorted

  head : ℕ → Sorted → ℕ
  head d nil = d
  head _ (cons x _ _) = x

mutual
  insert' : (x : ℕ) → Sorted → Sorted
  insert' x nil = nil
  insert' x (cons y l y≤hd_l) with x ≤? y
  ... | left e = cons x (cons y l y≤hd_l) e
  ... | right e = cons y (insert' x l) (insert'-lm l y≤hd_l e)

  insert'-lm : {x y : ℕ} → (l : Sorted) → (y ≤ head y l) → (y ≤ x) → (y ≤ head y (insert' x l))
  insert'-lm {x} {y} nil y≤hd_l y≤x = ≤-refl y
  insert'-lm {x} {y} (cons z l z≤hd_l) y≤z y≤x with x ≤? z
  ... | left e = y≤x
  ... | right e = y≤z

sort' : (l : List ℕ) → Sorted
sort' [] = nil
sort' (x ∷ l) = insert' x (sort' l)

data _∼_ {A : Set} : List A → List A → Set where
  ∼-nil : [] ∼ []
  ∼-drop : (x : A) {l l' : List A} → l ∼ l' → (x ∷ l) ∼ (x ∷ l')
  ∼-swap : (x y : A) (l : List A) → (x ∷ y ∷ l) ∼ (y ∷ x ∷ l)
  ∼-trans : {l l' l'' : List A} → l ∼ l' → l' ∼ l'' → l ∼ l''

-- ∼-refl : {A : Set} {l : List A} → l ∼ l
-- ∼-refl {A} {[]} = ∼-nil
-- ∼-refl {A} {x ∷ l} = ∼-drop x ∼-refl

-- ∼-sym : {A : Set} {l l' : List A} → l ∼ l' → l' ∼ l
-- ∼-sym {A} {.[]} {.[]} ∼-nil = ∼-nil
-- ∼-sym {A} {x ∷ l} {l'} l∼l' = {!   !}

split : {A : Set} → List A → List A × List A
split [] = [] , []
split (x ∷ []) = x ∷ [] , []
split (x ∷ y ∷ l) with split l
... | l1 , l2 = x ∷ l1 , y ∷ l2

test2 = split (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

-- {-# TERMINATING #-}
-- merge : (l m : List ℕ) → List ℕ
-- merge l [] = l
-- merge [] m = m
-- merge (x ∷ l) (y ∷ m) with x ≤? y
-- ... | left e = x ∷ merge l (y ∷ m)
-- ... | right e = y ∷ merge (x ∷ l) m

-- {-# TERMINATING #-}
-- mergesort : List ℕ → List ℕ
-- mergesort [] = []
-- mergesort (x ∷ []) = x ∷ []
-- mergesort l with split l
-- ... | a , b = merge (mergesort a) (mergesort b)

-- test-merge : List ℕ
-- test-merge = mergesort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

_<_ : ℕ → ℕ → Set
x < y = (suc x) ≤ y

length : {A : Set} (l : List A) → ℕ
length [] = zero
length (x ∷ l) = suc (length l)

split-fst-decr : (l : List ℕ) → (length (fst (split l))) ≤ (length l)
split-fst-decr [] = z≤n
split-fst-decr (x ∷ []) = s≤s z≤n
split-fst-decr (x ∷ y ∷ l) = s≤s (≤-trans (split-fst-decr l) (≤s (length l)))

split-snd-decr : (l : List ℕ) → (length (snd (split l))) ≤ (length l)
split-snd-decr [] = z≤n
split-snd-decr (x ∷ []) = z≤n
split-snd-decr (x ∷ y ∷ l) = s≤s (≤-trans (split-snd-decr l) (≤s (length l)))

merge'-full-lm : (x y : ℕ) → suc (x + y) ≤ (x + (suc y))
merge'-full-lm zero y = ≤-refl (suc y)
merge'-full-lm (suc x) y = s≤s (merge'-full-lm x y)

merge'-fuel : (n : ℕ) → (l m : List ℕ) → ((length l + length m) ≤ n) → List ℕ
merge'-fuel _ [] [] _ = []
merge'-fuel n [] (y ∷ m) _ = y ∷ m
merge'-fuel n (x ∷ l) [] _ = x ∷ l
merge'-fuel (suc n) (x ∷ l) (y ∷ m) l+m≤n with x ≤? y
... | left e = x ∷ merge'-fuel n l (y ∷ m) (≤-pred l+m≤n)
... | right e = y ∷ merge'-fuel n (x ∷ l) m (≤-pred (s≤s (≤-trans (merge'-full-lm (length l) (length m)) (≤-pred l+m≤n))))

merge' : (l m : List ℕ) → List ℕ
merge' l m = merge'-fuel (length l + length m) l m (≤-refl (length l + length m))

mergesort-fuel : (n : ℕ) → (l : List ℕ) → (length l ≤ n) → List ℕ
mergesort-fuel _ [] z≤n = []
mergesort-fuel n (x ∷ []) _ = x ∷ []
mergesort-fuel (suc n) (x ∷ y ∷ l) lenl≤n = merge'
  (mergesort-fuel n (x ∷ fst (split l)) (≤-pred (≤-trans (≤-suc (≤-suc (split-fst-decr l))) lenl≤n) ))
  (mergesort-fuel n (y ∷ snd (split l)) (≤-pred (≤-trans (≤-suc (≤-suc (split-snd-decr l))) lenl≤n)))

mergesort' : List ℕ → List ℕ
mergesort' l = mergesort-fuel (length l) l (≤-refl (length l))

merge'-sorting : (l m : List ℕ) → sorted l → sorted m → (sorted (merge' l m))
merge'-sorting [] [] s[] s[] = s[]
merge'-sorting [] (y ∷ m) s[] sortedym = sortedym
merge'-sorting (x ∷ l) [] sortedxl s[] = sortedxl
merge'-sorting (x ∷ l) (y ∷ m) (sl x≤*l sortedl) (sl y≤*m sortedm) with x ≤? y
... | left e = sl {!   !} (merge'-sorting l (y ∷ m) sortedl (sl y≤*m sortedm))
... | right e = {!   !}

mergesort-sorting : (l : List ℕ) → sorted (mergesort' l)
mergesort-sorting l = {!   !}

Rel : (A : Set) → Set₁
Rel A = A → A → Set

data Acc {A : Set} (_<_ : Rel A) (x : A) : Set where
  acc : ((y : A) → y < x → Acc _<_ y) → Acc _<_ x

WellFounded : {A : Set} → (_<_ : Rel A) → Set
WellFounded {A} _<_ = (x : A) → Acc _<_ x

postulate wfNatAxiom : WellFounded _<_
