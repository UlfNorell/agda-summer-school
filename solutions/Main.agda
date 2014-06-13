
open import Prelude
open import Data.Traversable

open import Term
open import Term.Parse
open import ScopeCheck
import TypeCheck
open import TypeCheckRaw
open import Term.Show
open import Lists

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
  flip (maybe (left parse-error)) (parseTerm s) $ λ e →
  TypeCheckRaw.checkedTerm <$> typeCheck [] e

main : IO Unit
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

runCompiled : String → Either TypeError (Σ Type SECD.Compiled.Value)
runCompiled s =
  parseAndTypeCheck s >>= λ r →
  pure $ second (SECD.Compiled.run ∘ compile) r

example =
 "let twice : (nat → nat) → nat → nat
            = λ (f : nat → nat) → λ (x : nat) → f (f x) in
  let times4 : (nat → nat) → nat → nat
             = λ (f : nat → nat) → twice (twice f) in
  let times16 : (nat → nat) → nat → nat
              = λ (f : nat → nat) → times4 (times4 f) in
  let times256 : (nat → nat) → nat → nat
               = λ (f : nat → nat) → times16 (times16 f) in
  times4 (times256 suc) 976"
