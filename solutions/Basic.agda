module Basic where

--: Define Bool

data Bool : Set where
  false : Bool
  true : Bool

--: Define not, and. Show case split, auto

not : Bool -> Bool
not false = true
not true = false

and : Bool -> Bool -> Bool
and false y = false
and true y = y

--: Rewrite type sigs, make mix-fix

¬_ : Bool → Bool
¬ false = true
¬ true = false

_∧_ : (_ _ : Bool) → Bool
false ∧ false = false
false ∧ true = false
true ∧ false = false
true ∧ true = true

--: Construct some bools, refine

_ : Bool
_ = (¬ false) ∧ (true ∧ false)

infixr 6 _∧_

_ : Bool
_ = true ∧ ¬ false ∧ false


--: Define Nat, _+_

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

num3 : Nat
num3 = suc (suc (suc zero))

_+_ : Nat → Nat → Nat
zero + y = y
suc x + y = suc (x + y)

--: Show BUILTIN, follow to stdlib

{-# BUILTIN NATURAL Nat #-}

-- open import Data.Nat
-- _ = ℕ

_*_ : Nat → Nat → Nat
zero * y = zero
suc x * y =  y + (x * y)

--: Reduce 0 + n, n + 0

-- _ : Nat → Nat
-- _ = λ n → {! n + 0 !}

--: Define List, Vector
--: Define length, append

infixr 6 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

-- open import Agda.Builtin.List

length : ∀ {A} → List A → Nat
length [] = 0
length (x ∷ l) = suc (length l)

append : ∀ {A} (_ _ : List A) → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

natlist : List Nat
natlist = 1 ∷ 2 ∷ 3 ∷ []

reverse : ∀ {A} → List A → List A
reverse [] = []
reverse (x ∷ xs) = append (reverse xs) (x ∷ [])



data Vector (A : Set) : Nat → Set where
  [] : Vector A 0
  _∷_ : {n : Nat} → A → Vector A n → Vector A (suc n)

vlength : ∀ {A n} → Vector A n → Nat
vlength {n = n} _ = n

vappend : ∀ {A n m} → Vector A n → Vector A m → Vector A (n + m)
vappend [] ys = ys
vappend (x ∷ xs) ys = x ∷ vappend xs ys


-- vreverse : ∀ {A n} → Vector A n → Vector A n
-- vreverse [] = []
-- vreverse (x ∷ xs) = {!vappend (vreverse xs) (x ∷ [])!}

vhead : ∀ {A n} → Vector A (suc n) → A
vhead (x ∷ xs) = x

vtail : ∀ {A n} → Vector A (suc n) → Vector A n
vtail (x ∷ xs) = xs

--------------------------------------------------------------------------------
--: Prove 0 + n ≡ n, n + 0 ≡ n

open import Agda.Builtin.Equality

zero-plus : (n : Nat) → 0 + n ≡ n
zero-plus n = refl

zero-plus′ : ∀ {n} → 0 + n ≡ n
zero-plus′ = refl

cong-suc : ∀ {n m} → n ≡ m → suc n ≡ suc m
cong-suc refl = refl

plus-zero : ∀ n → n + 0 ≡ n
plus-zero zero = refl
plus-zero (suc n) = cong-suc (plus-zero n)

plus-zero′ : ∀ n → n + 0 ≡ n
plus-zero′ zero = refl
plus-zero′ (suc n) rewrite plus-zero′ n = refl
