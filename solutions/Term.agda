
open import Prelude
open import Lists

infixr 7 _⇒_
data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

arrow-inj-dom : ∀ {a b a₁ b₁} → a ⇒ a₁ ≡ b ⇒ b₁ → a ≡ b
arrow-inj-dom refl = refl

arrow-inj-rng : ∀ {a b a₁ b₁} → a ⇒ a₁ ≡ b ⇒ b₁ → a₁ ≡ b₁
arrow-inj-rng refl = refl

private
  eqType : (a b : Type) → Dec (a ≡ b)
  eqType nat nat = yes refl
  eqType nat (b ⇒ b₁) = no (λ ())
  eqType (a ⇒ a₁) nat = no (λ ())
  eqType (a ⇒ a₁) ( b ⇒  b₁) with eqType a b
  eqType (a ⇒ a₁) ( b ⇒  b₁) | no neq = no λ eq → neq (arrow-inj-dom eq)
  eqType (a ⇒ a₁) (.a ⇒  b₁) | yes refl with eqType a₁ b₁
  eqType (a ⇒ a₁) (.a ⇒  b₁) | yes refl | no neq   = no λ eq → neq (arrow-inj-rng eq)
  eqType (a ⇒ a₁) (.a ⇒ .a₁) | yes refl | yes refl = yes refl

EqType : Eq Type
EqType = record { _==_ = eqType }

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

  erase : ∀ {Γ} → Term Γ → Unchecked.Term
  erase (var x _)   = var x
  erase (lit n)     = lit n
  erase suc         = suc
  erase (app u v)   = app (erase u) (erase v)
  erase (lam x a v) = lam x a (erase v)

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

  erase : ∀ {Γ a} → Term Γ a → WellScoped.Term (map fst Γ)
  erase (var x i)   = var x (map∈ fst i)
  erase (app u v)   = app (erase u) (erase v)
  erase (lam x a v) = lam x a (erase v)
  erase (lit n)     = lit n
  erase suc         = suc
