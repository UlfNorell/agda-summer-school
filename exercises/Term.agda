
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

module WellScoped where

  data Term (Γ : List Name) : Set where
    var : (x : Name) (i : x ∈ Γ) → Term Γ
    lit : (n : Nat) → Term Γ
    suc : Term Γ
    app : Term Γ → Term Γ → Term Γ
    lam : (x : Name) → Type → Term (x ∷ Γ) → Term Γ

  open Unchecked hiding (Term)

  -- Exercise: Define the erasure from well-scoped to unchecked terms.
  postulate
    erase : ∀ {Γ} → Term Γ → Unchecked.Term

module WellTyped where

  Cxt = List (Name × Type)

  data Term : Cxt → Type → Set where
    var : ∀ {Γ a} (x : Name) (i : (x , a) ∈ Γ) → Term Γ a
    app : ∀ {Γ a b} (u : Term Γ (a ⇒ b)) (v : Term Γ a) →
            Term Γ b
    lam : ∀ {Γ} x a {b} (v : Term ((x , a) ∷ Γ) b) → Term Γ (a ⇒ b)
    lit : ∀ {Γ} (n : Nat) → Term Γ nat
    suc : ∀ {Γ} → Term Γ (nat ⇒ nat)

  open WellScoped hiding (Term; erase)

  -- Exercise: Define the erasure from well-typed to well-scoped terms.
  postulate
    erase : ∀ {Γ a} → Term Γ a → WellScoped.Term (map fst Γ)
