
module TypeCheck where

open import Prelude
open import Lists

open import Term
open WellTyped
open Unchecked  renaming (Term to Expr)
open import Term.Show
open import Term.Parse

TypeError = String

TC : Set → Set
TC = Either TypeError

typeError : ∀ {A} → TypeError → TC A
typeError = left

data TypeChecked Γ : Expr → Set where
  ok : ∀ a (v : Term Γ a) → TypeChecked Γ (forgetTypes v)

data CheckedVar (Γ : Cxt) x : Set where
  ok : ∀ a (i : (x , a) ∈ Γ) → CheckedVar Γ x

-- Exercise: Implement the type checker. When you are done,
--           go to Lambda.agda and make it type check the
--           input and print the inferred type.
postulate typeCheck : ∀ Γ (e : Expr) → TC (TypeChecked Γ e)
-- typeCheck Γ e = ?

-- Forget which unchecked term we started with.
forgetOrigin : ∀ {Γ e} → TypeChecked Γ e → Σ Type (Term Γ)
forgetOrigin (ok a v) = a , v

parseAndTypeCheck : String → TC (Σ Type (Term []))
parseAndTypeCheck s =
  flip (maybe (typeError "Parse error")) (parseTerm s) $ λ e →
  forgetOrigin <$> typeCheck [] e

