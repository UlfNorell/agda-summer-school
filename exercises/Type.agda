
module Type where

open import Prelude

infixr 7 _=>_
data Type : Set where
  nat : Type
  _=>_ : (a b : Type) → Type

arrow-inj-dom : ∀ {a b a₁ b₁} → a => a₁ ≡ b => b₁ → a ≡ b
arrow-inj-dom refl = refl

arrow-inj-rng : ∀ {a b a₁ b₁} → a => a₁ ≡ b => b₁ → a₁ ≡ b₁
arrow-inj-rng refl = refl

private
  eqType : (a b : Type) → Dec (a ≡ b)
  eqType nat nat = yes refl
  eqType nat (b => b₁) = no (λ ())
  eqType (a => a₁) nat = no (λ ())
  eqType (a => a₁) ( b =>  b₁) with eqType a b
  eqType (a => a₁) ( b =>  b₁) | no neq = no λ eq → neq (arrow-inj-dom eq)
  eqType (a => a₁) (.a =>  b₁) | yes refl with eqType a₁ b₁
  eqType (a => a₁) (.a =>  b₁) | yes refl | no neq   = no λ eq → neq (arrow-inj-rng eq)
  eqType (a => a₁) (.a => .a₁) | yes refl | yes refl = yes refl

EqType : Eq Type
EqType = record { _==_ = eqType }

