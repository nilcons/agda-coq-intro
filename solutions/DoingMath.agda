module DoingMath where

--: Define Group

open import Agda.Builtin.Equality

record Group : Set₁ where
  field G : Set
  field _*_ : G → G → G
  infixl 7 _*_

  field assoc : ∀ {a b c} → (a * b) * c ≡ a * (b * c)

  field 𝟙 : G
  field lunit : ∀ {a} → 𝟙 * a ≡ a

  field _⁻¹ : G → G
  field linv : ∀ {a} → a ⁻¹ * a ≡ 𝟙
-- open Group public


record Group+ : Set₁ where
  field G : Set
  field _*_ : G → G → G
  infixl 7 _*_

  field assoc : ∀ {a b c} → (a * b) * c ≡ a * (b * c)

  field 𝟙 : G
  field lunit : ∀ {a} → 𝟙 * a ≡ a
  field runit : ∀ {a} → a * 𝟙 ≡ a

  field _⁻¹ : G → G
  field linv : ∀ {a} → a ⁻¹ * a ≡ 𝟙
  field rinv : ∀ {a} → a * a ⁻¹ ≡ 𝟙


group-group+ : Group → Group+
group-group+ = _

--------------------------------------------------------------------------------

record Group′ (G : Set) (_∙_ : G → G → G) : Set where
  field assoc : ∀ {a b c} → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)

  field 𝟙 : G
  field lunit : ∀ {a} → 𝟙 ∙ a ≡ a

  field _⁻¹ : G → G
  field linv : ∀ {a} → (a ⁻¹) ∙ a ≡ 𝟙

record Group′+ (G : Set) (_∙_ : G → G → G) : Set where
  field assoc : ∀ {a b c} → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)

  field 𝟙 : G
  field lunit : ∀ {a} → 𝟙 ∙ a ≡ a
  field runit : ∀ {a} → a ∙ 𝟙 ≡ a

  field _⁻¹ : G → G
  field linv : ∀ {a} → (a ⁻¹) ∙ a ≡ 𝟙
  field rinv : ∀ {a} → a ∙ (a ⁻¹) ≡ 𝟙

group-group′+ : ∀ {G mult} → Group′ G mult → Group′+ G mult
group-group′+ = _

--: Compare to Algebra.Structures
open import Algebra.Structures

--------------------------------------------------------------------------------

--: Formalization of a simple programming puzzle
--: https://eloquentjavascript.net/03_functions.html#h_jxl1p970Fy

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Bool
open import Relation.Nullary
open import Function.Equivalence

decide : ℕ → Bool
decide n with n % 5
... | 0 = false
... | 2 = 26 <ᵇ n
... | 4 = 8 <ᵇ n
{-# CATCHALL #-}
... | _ = true

infixr 6 _*3 _+5
data Times3Plus5 : ℕ → Set where
  start1 : Times3Plus5 1
  _*3 : ∀ {n} → Times3Plus5 n → Times3Plus5 (3 * n)
  _+5 : ∀ {n} → Times3Plus5 n → Times3Plus5 (5 + n)

ok8 : Times3Plus5 8
ok8 = start1 *3 +5

notok12 : ¬ (Times3Plus5 12)
notok12 = _

decide-correct : ∀ n → Times3Plus5 n ⇔ decide n ≡ true
decide-correct = _
