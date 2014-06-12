
module SECD.Compiled where

open import Prelude
open import Data.List

open import Term
open import ShowTerm
open Term.WellTyped
open import Sequence

StackType = List Type
Control : Cxt → StackType → StackType → Set

data Instr Γ : StackType → StackType → Set where
  access : ∀ {a Θ} x (i : (x , a) ∈ Γ) → Instr Γ Θ (a ∷ Θ)
  close  : ∀ {a b Θ} x → Control ((x , a) ∷ Γ) [] [ b ] → Instr Γ Θ (a ⇒ b ∷ Θ)
  call   : ∀ {a b Θ} → Instr Γ (a ⇒ b ∷ a ∷ Θ) (b ∷ Θ)
  lit    : ∀ {Θ} → Nat → Instr Γ Θ (nat ∷ Θ)
  suc    : ∀ {Θ} → Instr Γ Θ (nat ⇒ nat ∷ Θ)

Control Γ = Seq (Instr Γ)

compile′ : ∀ {Γ a Θ Δ} → Term Γ a → Control Γ (a ∷ Θ) Δ → Control Γ Θ Δ
compile′ (var x i)   c = access x i ∷ c
compile′ (app u v)   c = compile′ v $ compile′ u $ call ∷ c
compile′ (lam x a v) c = close x (compile′ v []) ∷ c
compile′ (lit n)     c = lit n ∷ c
compile′ suc         c = suc ∷ c

compile : ∀ {Γ a} → Term Γ a → Control Γ [] [ a ]
compile v = compile′ v []

data Value : Type → Set

Env : Cxt → Set
Env Γ = All (Value ∘ snd) Γ

data Value where
  lit     : Nat → Value nat
  suc     : Value (nat ⇒ nat)
  closure : ∀ {Γ a} (x : Name) b → Env Γ → Control ((x , b) ∷ Γ) [] [ a ] → Value (b ⇒ a)

Stack   = All Value

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

step (s ∣ e ∣ lit n ∷ c ∣ d) =
  next (lit n ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ access x i ∷ c ∣ d) =
  next (lookup∈ e i ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ suc ∷ c ∣ d) =
  next (suc ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ close x c′ ∷ c ∣ d) =
  next (closure x _ e c′ ∷ s ∣ e ∣ c ∣ d)

step (suc ∷ lit n ∷ s ∣ e ∣ call ∷ c ∣ d) =
  next (lit (suc n) ∷ s ∣ e ∣ c ∣ d)

step (closure x a e′ c′ ∷ v ∷ s ∣ e ∣ call ∷ c ∣ d) =
  next ([] ∣ v ∷ e′ ∣ c′ ∣ snapshot s e c ∷ d)

{-# NO_TERMINATION_CHECK #-}
run′ : ∀ {a} → SECD a → Value a
run′ s with step s
... | next s′ = run′ s′
... | done v  = v

run : ∀ {a} → Control [] [] [ a ] → Value a
run c = run′ ([] ∣ [] ∣ c ∣ [])

-- Show instance for values --

private
  showControl : ∀ {Γ Θ Δ} → Nat → Control Γ Θ Δ → ShowS
  showInstr : ∀ {Γ Θ Δ} → Nat → Instr Γ Θ Δ → ShowS
  showInstr p (access x i) = showParen (p > 9) $ showString ("access " & x)
  showInstr p (close x c)  = showParen (p > 9) $ showString ("close " & x & " ") ∘ showControl 10 c
  showInstr p call         = showString "call"
  showInstr p (lit n)      = shows n
  showInstr p suc          = showString "suc"

  showControl p []       = id
  showControl p (i ∷ []) = showInstr p i
  showControl p (i ∷ c)  = showParen (p > 0) $ showInstr 1 i ∘ showString "; " ∘ showControl 0 c

ShowInstr : ∀ {Γ Θ Δ} → Show (Instr Γ Θ Δ)
ShowInstr = record { showsPrec = showInstr }

ShowControl : ∀ {Γ Θ Δ} → Show (Control Γ Θ Δ)
ShowControl = record { showsPrec = showControl }

private
  showValue : ∀ {a} → Nat → Value a → ShowS
  showEnv   : ∀ {Γ} → Env Γ → ShowS

  showValue p (lit n)           = shows n
  showValue p suc               = showString "suc"
  showValue p (closure x a e c) = showParen (p > 0) $ showEnv e ∘ showString (" λ " & x & " → ") ∘ shows c

  showBinding : ∀ {a} → Name × Value a → ShowS
  showBinding (x , v) = showString x ∘ showString " = " ∘ showValue 0 v

  showEnv′ : ∀ {Γ} → Env Γ → ShowS
  showEnv′ []       = showString ""
  showEnv′ {Γ = (x , _) ∷ []} (v ∷ []) = showBinding (x , v)
  showEnv′ {Γ = (x , _) ∷ Γ } (v ∷ e)  = showBinding (x , v) ∘ showString ", " ∘ showEnv′ e

  showEnv e = showString "[" ∘ showEnv′ e ∘ showString "]"

ShowValue : ∀ {a} → Show (Value a)
ShowValue = record { showsPrec = showValue }
