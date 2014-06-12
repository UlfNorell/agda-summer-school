
open import Prelude
open import Data.List

open import Term
open import ScopeCheck hiding (Error; error; checkedTerm)
open WellTyped
open WellScoped renaming (Term to Expr) hiding (erase)
open import Term.Show

data TypeError : Set where
  scope-error : ScopeError → TypeError
  numbers-are-not-functions : ∀ {Γ a} → Term Γ nat → Term Γ a → TypeError
  argument-mismatch : ∀ {a′ b Γ} (a : Type) → Term Γ (a ⇒ b) → Term Γ a′ → TypeError

ShowTypeError : Show TypeError
ShowTypeError = record { showsPrec = λ p →
  λ { (scope-error e) → showsPrec p e
    ; (numbers-are-not-functions n v) →
         showParen (p > 0) $ showString "Cannot apply\n  "
                           ∘ shows n
                           ∘ showString "\nof type nat to argument\n"
                           ∘ shows v
    ; (argument-mismatch {a′ = a′} a f v) →
         showParen (p > 0) $ showString   "Expected type   : " ∘ shows a
                           ∘ showString "\nActual type     : " ∘ shows a′
                           ∘ showString "\nOf the argument : " ∘ shows v
                           ∘ showString "\nTo the function : " ∘ shows f
    } }

Error : Set → Set
Error = Either TypeError

error : ∀ {A} → TypeError → Error A
error = left

data TypeChecked Γ : Expr (map fst Γ) → Set where
  ok : ∀ a (v : Term Γ a) → TypeChecked Γ (erase v)

data OkVar (Γ : Cxt) x : x ∈ map fst Γ → Set where
  ok : ∀ a (i : (x , a) ∈ Γ) → OkVar Γ x (map∈ fst i)

lookupVarSuc : ∀ {y x Γ i} → OkVar Γ x i → OkVar (y ∷ Γ) x (suc i)
lookupVarSuc (ok a i) = ok a (suc i)

lookupVar : ∀ (Γ : Cxt) {x} (i : x ∈ map fst Γ) → OkVar Γ x i
lookupVar [] ()
lookupVar ((x , a) ∷ Γ) (zero refl) = ok a (zero refl)
lookupVar (_       ∷ Γ) (suc i)     = lookupVarSuc (lookupVar Γ i)  -- can't do with: issue1187

checkVar : ∀ {Γ x i} → OkVar Γ x i → TypeChecked Γ (var x i)
checkVar (ok a i) = ok a (var _ i)

checkApp : ∀ {Γ} {e₁ e₂ : Expr (map fst Γ)} →
           TypeChecked Γ e₁ →
           TypeChecked Γ e₂ → Either TypeError (TypeChecked Γ (app e₁ e₂))
checkApp (ok nat v) (ok a₁ v₁) = error (numbers-are-not-functions v v₁)
checkApp (ok (a ⇒ b) v) (ok a′ v₁) with a == a′
checkApp (ok (a ⇒ b) v) (ok .a v₁) | yes refl = pure (ok b (app v v₁))
checkApp (ok (a ⇒ b) v) (ok a′ v₁) | no _     = error (argument-mismatch a v v₁)

checkedLam : ∀ {Γ x a} {e : Expr (x ∷ map fst Γ)} →
             TypeChecked ((x , a) ∷ Γ) e → TypeChecked Γ (lam x a e)
checkedLam (ok _ v) = ok _ (lam _ _ v)

typeCheck : ∀ Γ (e : Expr (map fst Γ)) → Error (TypeChecked Γ e)
typeCheck Γ (var x i)   = pure $ checkVar (lookupVar Γ i)
typeCheck Γ (lit n)     = pure $ ok _ (lit n)
typeCheck Γ suc         = pure $ ok _ suc
typeCheck Γ (app e₁ e₂) = typeCheck Γ e₁ >>= λ v₁ →
                          typeCheck Γ e₂ >>= λ v₂ →
                          checkApp v₁ v₂ 
typeCheck Γ (lam x a e) = checkedLam <$> typeCheck ((x , a) ∷ Γ) e

checkedTerm : ∀ {Γ e} → TypeChecked Γ e → Σ Type (Term Γ)
checkedTerm (ok a v) = a , v
