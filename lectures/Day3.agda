-- An implementation of Landin's SECD machine. Adapted from
-- Danvy 2003 (A Rational Deconstruction of Landin's SECD Machine).
module Day3 where

open import Prelude

open import Term
open import Term.Show
open import Term.Parse
open Term.WellTyped
open import Lists

data Value : Type → Set

Env : Cxt → Set
Env Γ = All (λ { (x , a) → Value a }) Γ

data Value where
  lit     : Nat → Value nat
  suc     : Value (nat => nat)
  closure : ∀ {Γ a b} (x : Name) → Env Γ → Term ((x , a) ∷ Γ) b → Value (a => b)

StackType = List Type

data Directive Γ : StackType → StackType → Set where
  term  : ∀ {Δ a} → Term Γ a → Directive Γ Δ (a ∷ Δ)
  apply : ∀ {Δ a b} → Directive Γ (a => b ∷ a ∷ Δ) (b ∷ Δ)

Stack : StackType → Set
Stack Δ = All Value Δ

Control : Cxt → StackType → StackType → Set
Control Γ Δ Θ = Path (Directive Γ) Δ Θ

record Snapshot Θ a : Set where
  constructor snapshot
  field
    {Δ}         : StackType
    stack       : Stack Δ
    {Γ}         : Cxt
    environment : Env Γ
    control     : Control Γ (Θ ++ Δ) (a ∷ [])

Dump : Type → Type → Set
Dump = Path (λ a b → Snapshot (a ∷ []) b)

record SECD a : Set where
  constructor secd
  field
    {b}     : Type
    current : Snapshot [] b
    dump    : Dump b a

  open Snapshot current public

infix 1 _∣_∣_∣_
pattern _∣_∣_∣_ s e c d = secd (snapshot s e c) d

data StepResult a : Set where
  done  : Value a → StepResult a
  next  : SECD a → StepResult a

step : ∀ {a} → SECD a → StepResult a

step (v ∷ [] ∣ _ ∣ [] ∣ []) = done v

step (v ∷ [] ∣ _ ∣ [] ∣ snapshot s e c ∷ d) =
  next (v ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (lit n) ∷ c ∣ d) =
  next (lit n ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (var x i) ∷ c ∣ d) =
  next (lookup∈ e i ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term suc ∷ c ∣ d) =
  next (suc ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (lam x a t) ∷ c ∣ d) =
  next (closure x e t ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (app t₁ t₂) ∷ c ∣ d) =
  next (s ∣ e ∣ term t₂ ∷ term t₁ ∷ apply ∷ c ∣ d)

step (suc ∷ lit n ∷ s ∣ e ∣ apply ∷ c ∣ d) =
  next (lit (n + 1) ∷ s ∣ e ∣ c ∣ d)

step (closure x e′ t ∷ v ∷ s ∣ e ∣ apply ∷ c ∣ d) =
  next ([] ∣ v ∷ e′ ∣ term t ∷ [] ∣ (snapshot s e c) ∷ d)

{-# NO_TERMINATION_CHECK #-}
run′ : ∀ {a} → SECD a → Value a
run′ s with step s
... | next s′ = run′ s′
... | done v  = v

run : ∀ {a} → Term [] a → Value a
run t = run′ ([] ∣ [] ∣ term t ∷ [] ∣ [])

-- runUnchecked : String → Either String Value
-- runUnchecked s =
--   case parseTerm s of
--   λ { nothing  → left "parse error"
--     ; (just v) → run v
--     }

-- Show instance for values --

-- private
--   showValue : Nat → Value → ShowS
--   showEnv   : Env → ShowS

--   showValue p (lit n)         = shows n
--   showValue p suc             = showString "suc"
--   showValue p (closure x e v) = showParen (p > 0) $ showEnv e ∘ showString (" λ " & x & " → ") ∘ shows v

--   showBinding : Name × Value → ShowS
--   showBinding (x , v) = showString x ∘ showString " = " ∘ showValue 0 v

--   showEnv′ : Env → ShowS
--   showEnv′ []      = showString ""
--   showEnv′ [ b ]   = showBinding b
--   showEnv′ (b ∷ e) = showBinding b ∘ showString ", " ∘ showEnv′ e

--   showEnv e = showString "[" ∘ showEnv′ e ∘ showString "]"

-- ShowValue : Show Value
-- ShowValue = record { showsPrec = showValue }
