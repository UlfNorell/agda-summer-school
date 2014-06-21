
open import Prelude
open import Data.Traversable

open import Term
open import Term.Parse
open import TypeCheck
open import Term.Show
open import Lists

import SECD.Unchecked
import SECD.Compiled

open SECD.Unchecked  using (ShowValue)
open SECD.Compiled   using (compile)

open Unchecked  renaming (Term to Raw)
open WellScoped renaming (Term to Expr)
open WellTyped

ShowRes : Show (Either String SECD.Unchecked.Value)
ShowRes = ShowEither

main : IO Unit
main = getArgs >>= λ
       { [ file ] →
           readFile file >>= λ s →
           case parseTerm s of
           λ { nothing  → putStrLn "Parse error!"
             ; (just v) → putStrLn $ "Parsed: " & show v
                                    & "\nValue: " & show (SECD.Unchecked.run v)
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

example =
 "let twice    (f : nat → nat) (x : nat) : nat = f (f x)         in
  let times4   (f : nat → nat) : nat → nat = twice (twice f)     in
  let times16  (f : nat → nat) : nat → nat = times4 (times4 f)   in
  let times256 (f : nat → nat) : nat → nat = times16 (times16 f) in
  times4 (times256 suc) 976"
