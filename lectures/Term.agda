
module Term where

open import Prelude
open import Lists
open import Type public

Name = String

module Unchecked where

  data Term : Set where
    var : Name → Term
    lit : Nat → Term
    suc : Term
    app : Term → Term → Term
    lam : Name → Type → Term → Term

module WellTyped where

  Cxt = List (Name × Type)

  data Term (Γ : Cxt) : Type → Set where
    var : ∀ {a} (x : Name) (i : (x , a) ∈ Γ) → Term Γ a
    lit : Nat → Term Γ nat
    suc : Term Γ (nat => nat)
    app : ∀ {a b} → Term Γ (a => b) → Term Γ a → Term Γ b
    lam : ∀ {b} (x : Name) (a : Type) → Term ((x , a) ∷ Γ) b → Term Γ (a => b)

  open Unchecked renaming (Term to Expr)

  forgetTypes : ∀ {Γ a} → Term Γ a → Expr
  forgetTypes (var x i) = var x
  forgetTypes (lit x) = lit x
  forgetTypes suc = suc
  forgetTypes (app t t₁) = app (forgetTypes t) (forgetTypes t₁)
  forgetTypes (lam x a t) = lam x a (forgetTypes t)
