
open import Prelude
open import Lists

open import Term
open WellTyped  renaming (erase to eraseWellTyped)
open WellScoped using () renaming (erase to eraseWellScoped)
open Unchecked  renaming (Term to Expr)
open import Term.Show
open import Term.Parse

erase : ∀ {Γ a} → Term Γ a → Expr
erase = eraseWellScoped ∘ eraseWellTyped

data TypeError : Set where
  parse-error : TypeError

TC : Set → Set
TC = Either TypeError

typeError : ∀ {A} → TypeError → TC A
typeError = left

data TypeChecked Γ : Expr → Set where
  ok : ∀ a (v : Term Γ a) → TypeChecked Γ (erase v)

data CheckedVar (Γ : Cxt) x : Set where
  ok : ∀ a (i : (x , a) ∈ Γ) → CheckedVar Γ x

-- Exercise: Implement the type checker.
postulate typeCheck : ∀ Γ (e : Expr) → TC (TypeChecked Γ e)

checkedTerm : ∀ {Γ e} → TypeChecked Γ e → Σ Type (Term Γ)
checkedTerm (ok a v) = a , v

parseAndTypeCheck : String → TC (Σ Type (Term []))
parseAndTypeCheck s =
  flip (maybe (typeError parse-error)) (parseTerm s) $ λ e →
  checkedTerm <$> typeCheck [] e

-- Show instance for type errors --

ShowTypeError : Show TypeError
ShowTypeError = record { showsPrec = λ p →
  λ { parse-error → showParen (p > 0) $ showString "Parse error"
 -- ; more-cases-go-here → ? 
    } }

