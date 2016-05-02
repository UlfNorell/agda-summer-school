
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

eqType : (a b : Type) → Dec (a ≡ b)
eqType nat nat = yes refl
eqType nat (_ => _) = no λ ()
eqType (_ => _) nat = no λ ()
eqType (a => b) (a₁ => b₁) with eqType a a₁ | eqType b b₁
eqType (a => b) (.a => .b) | yes refl | yes refl = yes refl
... | yes _ | no ne  = no (ne ∘ arrow-inj-rng)
... | no ne | _      = no (ne ∘ arrow-inj-dom)

EqType : Eq Type
EqType = record { _==_ = eqType }
