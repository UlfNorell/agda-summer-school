
module Refl where

open import Prelude
open import Builtin.Reflection
open import Tactic.Nat

lem : ∀ a b c d → (a + b) + (c + d) ≡ c + (b + d) + a
lem a b c d = quoteGoal g in unquote (auto g)
