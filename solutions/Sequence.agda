
module Sequence where

open import Prelude

infixr 5 _∷_
data Seq {i e} {I : Set i} (E : I → I → Set e) : I → I → Set (i ⊔ e) where
  []  : ∀ {i} → Seq E i i
  _∷_ : ∀ {i j k} → E i j → Seq E j k → Seq E i k

_++ˢ_ : ∀ {i e} {I : Set i} {E : I → I → Set e} {i j k} → Seq E i j → Seq E j k → Seq E i k
[]       ++ˢ ys = ys
(x ∷ xs) ++ˢ ys = x ∷ xs ++ˢ ys
