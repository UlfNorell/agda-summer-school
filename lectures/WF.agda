
module WF where

open import Prelude
open import Control.WellFounded

-- {-# NO_TERMINATION_CHECK #-}
lem : ∀ a b → LessNat (a - b) (suc a)
lem a b = {!!}

divide-ish : (n : Nat) → Nat → Acc LessThan n → Nat
divide-ish  a       zero   _ = zero
divide-ish  zero   (suc b) _ = zero
divide-ish (suc a) (suc b) (acc f) =
  suc (divide-ish (a - b) (suc b) (f (a - b) (lem a b)))
