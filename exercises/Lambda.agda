
open import Prelude
open import Container.Traversable
open import System.File
open import System.FilePath

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

main : IO Unit
main = do
  [ file ] ← getArgs
    where _ → do p ← getProgName; putStrLn ("Usage: " & p & " FILE")
  s ← readTextFile (absolute file)
  case parseTerm s of λ where
    nothing  → putStrLn "Parse error!"
    (just v) → putStrLn $ "Parsed: " & show v
                        & "\nValue: " & show (SECD.Unchecked.run v)

-- For running from emacs.
-- For instance: C-c C-n runUnchecked "(λ (n : nat) → suc n) 5"
runUnchecked : String → Either String SECD.Unchecked.Value
runUnchecked s =
  case parseTerm s of λ where
    nothing  → left "parse error"
    (just v) → SECD.Unchecked.run v

example : String
example =
 "let twice    (f : nat → nat) (x : nat) : nat = f (f x)         in
  let times4   (f : nat → nat) : nat → nat = twice (twice f)     in
  let times16  (f : nat → nat) : nat → nat = times4 (times4 f)   in
  let times256 (f : nat → nat) : nat → nat = times16 (times16 f) in
  times4 (times256 suc) 976"
