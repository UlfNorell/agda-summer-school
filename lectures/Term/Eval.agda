
module Term.Eval where

open import Prelude

open import Lists
open import Term
open WellTyped

El : Type → Set
El nat      = Nat
El (a => b) = El a → El b

Env : Cxt → Set
Env Γ = All (El ∘ snd) Γ

-- Exercise: Implement an evaluator for well-typed terms.
postulate
  eval : ∀ {Γ a} → Term Γ a → Env Γ → El a
