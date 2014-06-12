
open import Prelude
open import Data.Traversable
open import Data.List

open import Term
open import ParseTerm
open import ScopeCheck
open import TypeCheck
open import ShowTerm

import SECD.Unchecked
import SECD.WellScoped
import SECD.StackSafe
import SECD.WellTyped
import SECD.Compiled

open SECD.Unchecked  using (ShowValue)
open SECD.WellScoped using (ShowValue)
open SECD.StackSafe  using (ShowValue)
open SECD.WellTyped  using (ShowValue)
open SECD.Compiled   using (ShowValue; ShowControl; compile)

open Unchecked  renaming (Term to Raw)
open WellScoped renaming (Term to Expr)
open WellTyped

parseAndScopeCheck : String → Either ScopeError (Expr [])
parseAndScopeCheck s = maybe (left parse-error) (λ e → ScopeCheck.checkedTerm <$> scopeCheck [] e) (parseTerm s)

parseAndTypeCheck : String → Either TypeError (Σ Type (Term []))
parseAndTypeCheck s =
  mapLeft scope-error (parseAndScopeCheck s) >>= λ e →
  TypeCheck.checkedTerm <$> typeCheck [] e

main : IO ⊤
main = getArgs >>= λ
       { [ file ] →
           readFile file >>= λ s →
           case parseAndTypeCheck s of
           λ { (left err)      → putStrLn $ "ERROR\n" & show err
             ; (right (a , v)) → putStrLn $ "OK\nTerm: " & show v
                                           & "\nType: " & show a
                                           & "\nCompiled: " & show (compile v)
                                           & "\nValue: " & show (SECD.Compiled.run (compile v))
             }
       ; _ → getProgName >>= λ p → putStrLn ("Usage: " & p & " FILE")
       }

Show₁ : Show (Σ Type (Term []))
Show₁ = ShowSigma {{ShowB = ShowTerm}}

Show₂ : Show (Either TypeError (Σ Type (Term [])))
Show₂ = ShowEither

runUnchecked : String → Either String SECD.Unchecked.Value
runUnchecked s =
  case parseTerm s of
  λ { nothing  → left "parse error"
    ; (just v) → SECD.Unchecked.run v
    }

runTypeSafe : String → Either TypeError (Σ Type SECD.WellTyped.Value)
runTypeSafe s =
  parseAndTypeCheck s >>= λ r →
  pure $ second SECD.WellTyped.run r
