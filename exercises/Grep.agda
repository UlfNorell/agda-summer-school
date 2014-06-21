
module Grep where

open import Prelude
open import Data.Traversable using (mapM)
open import Text.Printf
open import Lists

lines′ : List Char → List String
lines′ [] = []
lines′ ('\r' ∷ '\n' ∷ s) = "" ∷ lines′ s
lines′ ('\n' ∷ s)        = "" ∷ lines′ s
lines′ (c ∷ s)           = cons c (lines′ s)
  where
    cons : Char → List String → List String
    cons c (s ∷ ss) = (packString [ c ] & s) ∷ ss
    cons c [] = packString [ c ] ∷ []

lines : String → List String
lines = lines′ ∘ unpackString

-- Bonus exercise: Line numbers
--   Compute and print line numbers (represented by _∈_ or Any)
--   Might be useful to implement a variant of filterMaybe:
--     filterMaybeIx : {A : Set} {P : A → Set} → (∀ x → Maybe (P x)) →
--                     (xs : List A) → List (Σ A (λ x → x ∈ xs × P x)

-- Bonus exercise: More interesting matching
--   data Inside {A : Set} (xs ys : List A) : Set where
--     inside : ∀ pre suf → ys ≡ pre ++ xs ++ suf → Inside xs ys
--   Match word s = Inside (unpackString word) (unpackString s)

Match : String → String → Set
Match word s = s ≡ word

match : ∀ word s → Maybe (Match word s)
match word s =
  case s == word of
  λ { (yes eq) → just eq
    ; (no _)   → nothing }

grep : ∀ word s → List (Σ String (Match word))
grep word s = filterMaybe (match word) (lines s)

printLine : ∀ word → Σ String (Match word) → IO Unit
printLine word (s , m) = putStrLn $ printf "%s" s

main : IO Unit
main =
  getArgs >>= λ args →
  case args of
  λ { (word ∷ file ∷ []) →
      readFile file >>= λ s →
      unit <$ mapM (printLine word) (grep word s)
    ; _ →
      getProgName >>= λ prog →
      putStrLn ("USAGE: " & prog & " WORD FILE")
    }
