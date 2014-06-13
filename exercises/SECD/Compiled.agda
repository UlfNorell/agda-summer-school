
module SECD.Compiled where

open import Prelude
open import Lists

open import Term
open import Term.Show
open Term.Unchecked

Control : Set

data Instr : Set where
  access : Name → Instr
  close  : Name → Control → Instr
  call   : Instr
  lit    : Nat → Instr
  suc    : Instr

Control = List Instr

compile′ : Term → Control → Control
compile′ (var x)     c = access x ∷ c
compile′ (app u v)   c = compile′ v $ compile′ u $ call ∷ c
compile′ (lam x a v) c = close x (compile′ v []) ∷ c
compile′ (lit n)     c = lit n ∷ c
compile′ suc         c = suc ∷ c

compile : Term → Control
compile v = compile′ v []

-- Exercise:
--   Make the instruction set above type safe and modify (a copy of) the
--   WellTyped SECD machine to use this representation of the control
--   component.