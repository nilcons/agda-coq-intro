module PropositionsAsTypes where

--: Claim: propositions can be thought of as types, with methods of
--: proving them (aka. their proofs) as elements.
--:
--: Lets check!

--: Is (D → C) → ((B → (C → A)) → (D → (B → A))) true?
--: When is an implication true?

complicated : ∀ {A B C D : Set} → (D → C) → (B → C → A) → D → B → A
complicated dc bca d b = bca b (dc d)

--: Is (D → B) → (B → C → A) → D → B → A true?
-- complicated2 : ∀ {A B C D : Set} → (D → B) → (B → C → A) → D → B → A
-- complicated2 db bca d b = {!!}

--: Implicational Propositional Calculus is complete with two axioms:
--: P → Q → P
--: (P → Q → R) → (P → Q) → P → R
--:
--: with modus ponens as the single inference rule
--: P → Q, P
--: ---------
--:     Q

K : ∀ {P Q : Set} → P → Q → P
K x _ = x

S : ∀ {P Q R : Set} → (P → Q → R) → (P → Q) → P → R
S x y z = x z (y z)


--: OK, what about other logical connectives?
--: A ∧ B?

infixl 6 _∧_
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

--: Truth, Falsity?

-- data True : Set where
--   trivial : True

-- This is fancy for the SortedList example:
record True : Set where
  constructor trivial

data False : Set where

--: Everything implies True
--: From False follows anything
--: ¬ A?

everything-implies-true : ∀ {A : Set} → A → True
everything-implies-true _ = trivial

false-implies-anything : ∀ {A : Set} → False → A
false-implies-anything ()

infix 7 ¬_
¬_ : Set → Set
¬ A = (A → False)

--: Logical Or?

infixl 5 _∨_
data _∨_ (A B : Set) : Set where
  left-true  : A → A ∨ B
  right-true : B → A ∨ B

--: Usual De Morgan laws?

¬∨-∧¬ : ∀ {A B : Set} → ¬ (A ∨ B) → ¬ A ∧ ¬ B
¬∨-∧¬ nab = (λ a → nab (left-true a)) , (λ z → nab (right-true z))

¬∧-∨¬ : ∀ {A B : Set} → ¬ (A ∧ B) → ¬ A ∨ ¬ B
¬∧-∨¬ = _

--: Constructive logic, LEM

lem : ∀ {A : Set} → A ∨ ¬ A
lem = _


--: Predicates? Functions that return types
--: ≤ : Nat → Nat → Prop

open import Agda.Builtin.Nat

_≤_ : Nat → Nat → Set
zero ≤ m = True
suc n ≤ zero = False
suc n ≤ suc m = n ≤ m


--: Can use it as an actual precondition

nat-minus : (n m : Nat) → (m ≤ n) → Nat
nat-minus n zero mn = n
-- nat-minus zero (suc m) mn = false-implies-anything mn
nat-minus zero (suc m) ()
nat-minus (suc n) (suc m) mn = nat-minus n m mn


--: Forall? Exists?
--: ∀ (n : Nat), n ≤ n
--: ∃ (n : Nat), n ≥ 3

-- Generally when B : A → Set, then ∀ (x : A) → B x is dependent
-- function space.

n≤n : ∀ (n : Nat) → n ≤ n
n≤n zero = trivial
n≤n (suc n) = n≤n n

data ∃ {A : Set} (B : A → Set) : Set where
  _,_ : (a : A) → (b : B a) → ∃ B

n≥3 : ∃ (λ n → 3 ≤ n)
n≥3 = 3 , trivial


--: Sorted List, by construction?

-- infixr 6 _∷⟨_⟩_
infixr 6 _∷_
data SBList (lb : Nat) : Set where
  [] : SBList lb
  -- _∷⟨_⟩_ : (n : Nat) → (lb ≤ n) → SBList n → SBList lb
  _∷_ : (n : Nat) → {lb ≤ n} → SBList n → SBList lb

SortedList : Set
SortedList = SBList 0

_ : SortedList
-- _ = 3 ∷⟨ trivial ⟩ 5 ∷⟨ trivial ⟩ 10 ∷⟨ trivial ⟩ []
_ = 3 ∷ 5 ∷ 10 ∷ []
