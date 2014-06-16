
module Term.Eval where

open import Prelude

open import Lists
open import Term
open WellTyped

El : Type → Set
El nat = Nat
El (a ⇒ b) = El a → El b

-- Exercise: Implement an evaluator for well-typed terms.
postulate
  Env : Cxt → Set
  eval : ∀ {Γ a} → Term Γ a → Env Γ → El a
