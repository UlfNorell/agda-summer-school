
module Term.Eval where

open import Prelude

open import Lists
open import Term
open WellTyped

El : Type → Set
El nat = Nat
El (a ⇒ b) = El a → El b

-- Exercise: Implement an evaluator for well-typed terms.
Env : Cxt → Set
Env Γ = All (El ∘ snd) Γ

eval : ∀ {Γ a} → Term Γ a → Env Γ → El a
eval (var x i)   env = lookup∈ env i
eval (app u v)   env = eval u env (eval v env)
eval (lam x a v) env = λ u → eval v (u ∷ env)
eval (lit n)     env = n
eval suc         env = suc
