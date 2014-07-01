
open import Prelude
open import Lists

open import Term
open WellTyped
open Unchecked renaming (Term to Expr)
open import Term.Parse
open import Term.Show

TypeError : Set
TypeError = String

TC : Set → Set
TC A = Either TypeError A

typeError : ∀ {A} → TypeError → TC A
typeError err = left err

data Checked (Γ : Cxt) : Expr → Set where
  ok : ∀ a (v : Term Γ a) → Checked Γ (forgetTypes v)

lookupVar : (Γ : Cxt) (x : Name) → TC (Σ Type λ a → (x , a) ∈ Γ)
lookupVar [] x = typeError ("Variable out of scope: " & x)
lookupVar ((y , a) ∷ Γ) x with x == y
lookupVar ((y , a) ∷ Γ) .y | yes refl = return (a , zero refl)
lookupVar ((y , a) ∷ Γ) x  | no _ = fmap (second suc) (lookupVar Γ x)

checkedVar : ∀ {Γ x} → Σ Type (λ a → (x , a) ∈ Γ) → Checked Γ (var x)
checkedVar (a , i) = ok a (var _ i)

checkedLam : ∀ {Γ x a e} → Checked ((x , a) ∷ Γ) e → Checked Γ (lam x a e)
checkedLam (ok b v) = ok (_ => b) (lam _ _ v)

checkApp : ∀ {Γ e e₁} → Checked Γ e → Checked Γ e₁ → TC (Checked Γ (app e e₁))
checkApp (ok nat v) (ok a₁ v₁) = typeError ("nat is not a fun: " & show v)
checkApp (ok (a => b) v) (ok a₁ v₁) with a == a₁
checkApp (ok (a => b) v) (ok .a v₁) | yes refl = right (ok b (app v v₁))
checkApp (ok (a => b) v) (ok a₁ v₁) | no _   = typeError "argument mismatch"

typeCheck : (Γ : Cxt) (e : Expr) → TC (Checked Γ e)
typeCheck Γ (var x) = fmap checkedVar (lookupVar Γ x)
typeCheck Γ (lit n) = right (ok nat (lit n))
typeCheck Γ suc = right (ok (nat => nat) suc)
typeCheck Γ (app e e₁) =
  typeCheck Γ e  >>= λ v →
  typeCheck Γ e₁ >>= λ v₁ →
  checkApp v v₁
typeCheck Γ (lam x a e) = fmap checkedLam (typeCheck ((x , a) ∷ Γ) e)

forgetOrigin : ∀ {Γ e} → Checked Γ e → Σ Type (Term Γ)
forgetOrigin (ok a v) = a , v

parseAndTypeCheck : String → TC (Σ Type (Term []))
parseAndTypeCheck s =
  case parseTerm s of
  λ { nothing  → typeError "parse error"
    ; (just e) → fmap forgetOrigin (typeCheck [] e) }
