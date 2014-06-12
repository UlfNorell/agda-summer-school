
module SECD.WellTyped where

open import Prelude
open import Data.List

open import Term
open import Term.Show
open Term.WellTyped
open import Sequence

data Value : Type → Set

Env : Cxt → Set
Env Γ = All (Value ∘ snd) Γ

data Value where
  lit     : Nat → Value nat
  suc     : Value (nat ⇒ nat)
  closure : ∀ {Γ a} (x : Name) b → Env Γ → Term ((x , b) ∷ Γ) a → Value (b ⇒ a)

StackType = List Type

data Directive Γ : StackType → StackType → Set where
  term  : ∀ {a Θ} → Term Γ a → Directive Γ Θ (a ∷ Θ)
  apply : ∀ {a b Θ} → Directive Γ (a ⇒ b ∷ a ∷ Θ) (b ∷ Θ)

Stack   = All Value
Control = λ Γ → Seq (Directive Γ)

record Snapshot Δ a : Set where
  constructor snapshot
  field
    {Θ}         : StackType
    stack       : Stack Θ
    {Γ}         : Cxt
    environment : Env Γ
    control     : Control Γ (Δ ++ Θ) [ a ]

Dump = Seq (λ a b → Snapshot [ a ] b)

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

step (v ∷ [] ∣ e′ ∣ [] ∣ (snapshot s e c) ∷ d) =
  next (v ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (lit n) ∷ c ∣ d) =
  next (lit n ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (var x i) ∷ c ∣ d) =
  next (lookup∈ e i ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term suc ∷ c ∣ d) =
  next (suc ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (lam x a t) ∷ c ∣ d) =
  next (closure x a e t ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (app t₁ t₂) ∷ c ∣ d) =
  next (s ∣ e ∣ term t₂ ∷ term t₁ ∷ apply ∷ c ∣ d)

step (suc ∷ lit n ∷ s ∣ e ∣ apply ∷ c ∣ d) =
  next (lit (suc n) ∷ s ∣ e ∣ c ∣ d)

step (closure x a e′ t ∷ v ∷ s ∣ e ∣ apply ∷ c ∣ d) =
  next ([] ∣ v ∷ e′ ∣ term t ∷ [] ∣ snapshot s e c ∷ d)

{-# NO_TERMINATION_CHECK #-}
run′ : ∀ {a} → SECD a → Value a
run′ s with step s
... | next s′ = run′ s′
... | done v  = v

run : ∀ {a} → Term [] a → Value a
run t = run′ ([] ∣ [] ∣ term t ∷ [] ∣ [])

-- Show instance for values --

private
  showValue : ∀ {a} → Nat → Value a → ShowS
  showEnv   : ∀ {Γ} → Env Γ → ShowS

  showValue p (lit n)           = shows n
  showValue p suc               = showString "suc"
  showValue p (closure x a e v) = showParen (p > 0) $ showEnv e ∘ showString " " ∘ shows (lam x a v)

  showBinding : ∀ {a} → Name × Value a → ShowS
  showBinding (x , v) = showString x ∘ showString " = " ∘ showValue 0 v

  showEnv′ : ∀ {Γ} → Env Γ → ShowS
  showEnv′ []       = showString ""
  showEnv′ {Γ = (x , _) ∷ []} (v ∷ []) = showBinding (x , v)
  showEnv′ {Γ = (x , _) ∷ Γ } (v ∷ e)  = showBinding (x , v) ∘ showString ", " ∘ showEnv′ e

  showEnv e = showString "[" ∘ showEnv′ e ∘ showString "]"

ShowValue : ∀ {a} → Show (Value a)
ShowValue = record { showsPrec = showValue }
