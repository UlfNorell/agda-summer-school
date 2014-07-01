
module SizedTypes where

open import Prelude
open import Builtin.Size

data SNat : {_ : Size} → Set where
  zero : ∀ {i} → SNat {↑ i}
  suc  : ∀ {i} → SNat {i} → SNat {↑ i}

fromNat : Nat → SNat
fromNat  zero   = zero
fromNat (suc n) = suc (fromNat n)

toNat : SNat → Nat
toNat  zero   = zero
toNat (suc n) = suc (toNat n)

minus : ∀ {i} → SNat {i} → Nat → SNat {i}
minus  n       zero   = n
minus  zero   (suc m) = zero
minus (suc n) (suc m) = minus n m

divide-ish : ∀ {i} → SNat {i} → Nat → Nat
divide-ish  a       zero   = zero
divide-ish  zero   (suc b) = zero
divide-ish .{↑ i} (suc {i} a) (suc b) = suc (divide-ish {i} (minus a b) (suc b))
