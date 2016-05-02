
module Term.Show where

open import Prelude

open import Term
open Unchecked renaming (Term to Raw)
open WellScoped renaming (Term to Expr)
open WellTyped

private
  showType : Nat → Type → ShowS
  showType p nat      = showString "nat"
  showType p (a => b) = showParen (p >? 7) $ showType 8 a ∘ showString " → " ∘ showType 7 b

instance
  ShowType : Show Type
  ShowType = record { showsPrec = showType }

private
  showRaw : Nat → Raw → ShowS
  showRaw p (var x)     = showString x
  showRaw p (lit n)     = shows n
  showRaw p suc         = showString "suc"
  showRaw p (app e e₁)  = showParen (p >? 9) $ showRaw 9 e ∘ showString " " ∘ showRaw 10 e₁
  showRaw p (lam x a e) = showParen (p >? 0) $ showString ("λ (" & x & " : ")
                                             ∘ shows a ∘ showString ") → " ∘ showRaw 0 e

instance
  ShowRaw : Show Raw
  ShowRaw = record { showsPrec = showRaw }

  ShowExpr : ∀ {Γ} → Show (Expr Γ)
  ShowExpr = ShowBy forgetScope

ShowTerm : ∀ {Γ a} → Show (Term Γ a)
ShowTerm = ShowBy forgetTypes
