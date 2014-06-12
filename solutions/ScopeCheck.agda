
open import Prelude
open import Data.List

open import Term
open Unchecked renaming (Term to RawTerm)
open WellScoped

data ScopeError : Set where
  out-of-scope : Name → ScopeError
  parse-error  : ScopeError

ShowScopeError : Show ScopeError
ShowScopeError = record { showsPrec = λ p →
  λ { (out-of-scope x) → showParen (p > 0) $ showString ("Variable out of scope: " & x)
    ; parse-error      → showParen (p > 0) $ showString "Parse error"
    } }

Error : Set → Set
Error = Either ScopeError

error : ∀ {A} → ScopeError → Error A
error = left

find : ∀ (x : Name) Γ → Error (x ∈ Γ)
find x [] = error (out-of-scope x)
find y ( x ∷ xs) with x == y
find x (.x ∷ xs)    | yes refl = pure (zero refl)
find x ( y ∷ xs)    | no _     = suc <$> find x xs

data ScopeChecked Γ : RawTerm → Set where
  ok : (t : Term Γ) → ScopeChecked Γ (erase t)

checkedTerm : ∀ {Γ e} → ScopeChecked Γ e → Term Γ
checkedTerm (ok t) = t

okVar : ∀ {Γ} x → x ∈ Γ → ScopeChecked Γ (var x)
okVar x i = ok (var x i)

okApp : ∀ {Γ u v} → ScopeChecked Γ u → ScopeChecked Γ v → ScopeChecked Γ (app u v)
okApp (ok u) (ok v) = ok (app u v)

okLam : ∀ {Γ v} x a → ScopeChecked (x ∷ Γ) v → ScopeChecked Γ (lam x a v)
okLam x a (ok v) = ok (lam x a v)

scopeCheck : ∀ Γ (e : RawTerm) → Error (ScopeChecked Γ e)
scopeCheck Γ (var x)     = okVar x <$> find x Γ
scopeCheck Γ (lit n)     = pure $ ok (lit n)
scopeCheck Γ suc         = pure $ ok suc
scopeCheck Γ (app u v)   = okApp <$> scopeCheck Γ u <*> scopeCheck Γ v
scopeCheck Γ (lam x a v) = okLam x a <$> scopeCheck (x ∷ Γ) v
