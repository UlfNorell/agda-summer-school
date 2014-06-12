
open import Prelude
open import Data.List
open import Term
open WellTyped

find : (Γ : Cxt) (x : Name) → Maybe (Σ Type λ a → (x , a) ∈ Γ)
find [] x = nothing
find ((x , a) ∷ Γ) y with x == y
find ((x , a) ∷ Γ) .x | yes refl = just (a , zero refl)
find ((x , a) ∷ Γ) y  | no _     = (id *** suc) <$> find Γ y

find! : ∀ Γ x {{_ : IsJust (find Γ x)}} → Σ _ λ a → (x , a) ∈ Γ
find! Γ x = fromJust (find Γ x)

var! : ∀ {Γ} x {_ : IsJust (find Γ x)} → Term Γ (fst (find! Γ x))
var! {Γ} x = var x (snd (find! Γ x))

tId : ∀ {Γ a} → Term Γ (a ⇒ a)
tId = lam "x" _ (var! "x")

ex₁ : ∀ {Γ a} → Term Γ (a ⇒ a)
ex₁ = app tId tId

plus-one : ∀ {Γ} → Term Γ (nat ⇒ nat)
plus-one = lam "n" _ (app suc (var! "n"))

twice : ∀ {Γ a} → Term Γ ((a ⇒ a) ⇒ a ⇒ a)
twice {a = a} = lam "f" _ $ lam "x" _ $ app (var! "f") $ app (var! "f") (var! "x")

five : ∀ {Γ} → Term Γ _
five = app plus-one (lit 4)

seven : ∀ {Γ} → Term Γ _
seven = app (app twice plus-one) five
