
module Type where

open import Prelude
open import Tactic.Deriving.Eq

infixr 7 _=>_
data Type : Set where
  nat : Type
  _=>_ : (a b : Type) → Type

arrow-inj-dom : ∀ {a b a₁ b₁} → a => a₁ ≡ b => b₁ → a ≡ b
arrow-inj-dom refl = refl

arrow-inj-rng : ∀ {a b a₁ b₁} → a => a₁ ≡ b => b₁ → a₁ ≡ b₁
arrow-inj-rng refl = refl

unquoteDecl eqType = derivingEq (quote Type) eqType

instance
  EqType : Eq Type
  EqType = record { _==_ = eqType }

