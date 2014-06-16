
module SECD.StackSafe where

open import Prelude

open import Term
open import Term.Show
open import Term.Parse
open Term.Unchecked
open import Lists

data Value : Set
Env = List (Name × Value)

data Value where
  lit     : Nat → Value
  suc     : Value
  closure : Name → Env → Term → Value

data Directive : Nat → Nat → Set where
  term  : ∀ {n} → Term → Directive n (1 + n)
  apply : ∀ {n} → Directive (2 + n) (1 + n)

Stack   = Vec Value
Control = Path Directive

record Snapshot j : Set where
  constructor snapshot
  field
    {n}         : Nat
    stack       : Stack n
    environment : Env
    control     : Control (j + n) 1

Dump = List (Snapshot 1)

record SECD : Set where
  constructor secd
  field
    current : Snapshot 0
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

step (lit _ ∷ _ ∷ _           ∣ _ ∣ apply ∷ _ ∣ _) = error "apply literal"
step (suc ∷ suc ∷ _           ∣ _ ∣ apply ∷ _ ∣ _) = error "apply suc to suc"
step (suc ∷ closure _ _ _ ∷ _ ∣ _ ∣ apply ∷ _ ∣ _) = error "apply suc to closure"

{-# NO_TERMINATION_CHECK #-}
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
  showValue p (closure x e v) = showParen (p > 0) $ showEnv e ∘ showString (" λ " & x & " → ") ∘ shows v

  showBinding : Name × Value → ShowS
  showBinding (x , v) = showString x ∘ showString " = " ∘ showValue 0 v

  showEnv′ : Env → ShowS
  showEnv′ []      = showString ""
  showEnv′ [ b ]   = showBinding b
  showEnv′ (b ∷ e) = showBinding b ∘ showString ", " ∘ showEnv′ e

  showEnv e = showString "[" ∘ showEnv′ e ∘ showString "]"

ShowValue : Show Value
ShowValue = record { showsPrec = showValue }
