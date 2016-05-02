-- An implementation of Landin's SECD machine. Adapted from
-- Danvy 2003 (A Rational Deconstruction of Landin's SECD Machine).
module SECD.Unchecked where

open import Prelude

open import Term
open import Term.Show
open Term.Unchecked

data Value : Set
Env = List (Name × Value)

data Value where
  lit     : Nat → Value
  suc     : Value
  closure : Name → Env → Term → Value

data Directive : Set where
  term  : Term → Directive
  apply : Directive

Stack   = List Value
Control = List Directive

record Snapshot : Set where
  constructor snapshot
  field
    stack       : Stack
    environment : Env
    control     : Control

Dump = List Snapshot

record SECD : Set where
  constructor secd
  field
    current : Snapshot
    dump    : Dump

  open Snapshot current public

infix 1 _∣_∣_∣_
pattern _∣_∣_∣_ s e c d = secd (snapshot s e c) d

data StepResult : Set where
  done  : Value → StepResult
  next  : SECD → StepResult
  error : String → StepResult

step : SECD → StepResult

step (v ∷ [] ∣ _ ∣ [] ∣ []) = done v

step (v ∷ [] ∣ e′ ∣ [] ∣ (snapshot s e c) ∷ d) =
  next (v ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (lit n) ∷ c ∣ d) =
  next (lit n ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (var x) ∷ c ∣ d) =
  case lookup e x of
  λ { nothing  → error ("variable out of scope: " & x)
    ; (just v) → next (v ∷ s ∣ e ∣ c ∣ d) }

step (s ∣ e ∣ term suc ∷ c ∣ d) =
  next (suc ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (lam x a t) ∷ c ∣ d) =
  next (closure x e t ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (app t₁ t₂) ∷ c ∣ d) =
  next (s ∣ e ∣ term t₂ ∷ term t₁ ∷ apply ∷ c ∣ d)

step (suc ∷ lit n ∷ s ∣ e ∣ apply ∷ c ∣ d) =
  next (lit (suc n) ∷ s ∣ e ∣ c ∣ d)

step (closure x e′ t ∷ v ∷ s ∣ e ∣ apply ∷ c ∣ d) =
  next ([] ∣ (x , v) ∷ e′ ∣ term t ∷ [] ∣ (snapshot s e c) ∷ d)

step ([]                      ∣ _ ∣ []        ∣ _) = error "empty stack on return"
step (_ ∷ _ ∷ _               ∣ _ ∣ []        ∣ _) = error "more than one stack element on return"
step ([]                      ∣ _ ∣ apply ∷ _ ∣ _) = error "apply on empty stack"
step (_ ∷ []                  ∣ _ ∣ apply ∷ _ ∣ _) = error "apply on singleton stack"
step (lit _ ∷ _ ∷ _           ∣ _ ∣ apply ∷ _ ∣ _) = error "apply literal"
step (suc ∷ suc ∷ _           ∣ _ ∣ apply ∷ _ ∣ _) = error "apply suc to suc"
step (suc ∷ closure _ _ _ ∷ _ ∣ _ ∣ apply ∷ _ ∣ _) = error "apply suc to closure"

{-# NON_TERMINATING #-}
run′ : SECD → Either String Value
run′ s with step s
... | next s′ = run′ s′
... | done v  = right v
... | error e = left e

run : Term → Either String Value
run t = run′ ([] ∣ [] ∣ term t ∷ [] ∣ [])

-- Show instance for values --

private
  showValue : Nat → Value → ShowS
  showEnv   : Env → ShowS

  showValue p (lit n)         = shows n
  showValue p suc             = showString "suc"
  showValue p (closure x e v) = showParen (p >? 0) $ showEnv e ∘ showString (" λ " & x & " → ") ∘ shows v

  showBinding : Name × Value → ShowS
  showBinding (x , v) = showString x ∘ showString " = " ∘ showValue 0 v

  showEnv′ : Env → ShowS
  showEnv′ []      = showString ""
  showEnv′ [ b ]   = showBinding b
  showEnv′ (b ∷ e) = showBinding b ∘ showString ", " ∘ showEnv′ e

  showEnv e = showString "[" ∘ showEnv′ e ∘ showString "]"

instance
  ShowValue : Show Value
  ShowValue = record { showsPrec = showValue }
