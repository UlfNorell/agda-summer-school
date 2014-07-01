{-# OPTIONS --copatterns #-}

module Stream where

open import Prelude

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream

ones : Stream Nat
head ones = 1
tail ones = ones

nats : Nat → Stream Nat
head (nats zero) = 1
head (nats (suc n)) = suc n
tail (nats n) = nats (suc n)

fib : Stream Nat
head fib        = 0
head (tail fib) = 1
tail (tail fib) = {!!}

record CoList (A : Set) : Set

data CoListP (A : Set) : Set where
  [] : CoListP A
  _∷_ : A → CoList A → CoListP A

record CoList A where
  coinductive
  field
    observe : CoListP A

open CoList

ones′ : CoList Nat
observe ones′ = 1 ∷ ones′

head′ : {A : Set} → CoList A → Maybe A
head′ xs =
  case observe xs of
  λ { [] → nothing
    ; (x ∷ xs) → just x }

tail′ : {A : Set} → CoList A → Maybe (CoList A)
tail′ xs =
  case observe xs of
  λ { [] → nothing
    ; (x ∷ xs) → just xs }

thm : tail′ ones′ ≡ just ones′
thm = refl
