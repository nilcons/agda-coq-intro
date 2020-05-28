module PropositionsAsTypes where

--: Claim: propositions can be thought of as types, with methods of
--: proving them (aka. their proofs) as elements.
--:
--: Lets check!

--: Is (D → C) → ((B → (C → A)) → (D → (B → A))) true?
--: When is an implication true?

complicated : ∀ {A B C D : Set} → (D → C) → (B → C → A) → D → B → A
complicated = _

--: Is (D → B) → (B → C → A) → D → B → A true?
complicated2 : ∀ {A B C D : Set} → (D → B) → (B → C → A) → D → B → A
complicated2 = _



























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



--: Truth, Falsity?



--: Everything implies True
--: From False follows anything
--: ¬ A?



--: Logical Or?

--: Usual De Morgan laws?

-- ¬∨-∧¬ : ∀ {A B : Set} → ¬ (A ∨ B) → ¬ A ∧ ¬ B
-- ¬∨-∧¬ nab = ?

-- ¬∧-∨¬ : ∀ {A B : Set} → ¬ (A ∧ B) → ¬ A ∨ ¬ B
-- ¬∧-∨¬ = _

--: Constructive logic, LEM

-- lem : ∀ {A : Set} → A ∨ ¬ A
-- lem = _


--: Predicates? Functions that return types
--: ≤ : Nat → Nat → Prop


--: Can use it as an actual precondition
--: Proper Nat subtraction?


--: Forall? Exists?
--: ∀ (n : Nat), n ≤ n
--: ∃ (n : Nat), n ≥ 3


--: Sorted List, by construction?
