{-# OPTIONS --safe #-}

module compared-to-haskell where

open import Data.Nat

factorial : ℕ → ℕ
factorial zero = 1
factorial n@(suc n′) = n * factorial n′

{- Visible differences:
   - Upper/lower case don't matter syntactically, just convention
   - Swapped : and ::  :D
   - more lenient identifier naming rules
   - Unicode
-}

{- Syntax:
   - very simple tokenizer
   - almost any string is a valid identifier, exceptions: whitespace () {} _ . "
-}

open import Agda.Builtin.Equality


+-comm : ∀ {x y x+y} → x + y ≡ x+y → y + x ≡ x+y
+-comm = _

-- Most devious:
-- swap (x , y) = (y , x)

