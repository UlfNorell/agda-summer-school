
module Term.Parse where

open import Prelude
import Text.Parse as P

open import Term.Lex
open import Term
open Term.Unchecked
open P Token

pi : P String
pi = symbol >>= λ
      { (ti x) → return x
      ; _      → fail }

pn : P Nat
pn = symbol >>= λ
       { (tn n) → return n
       ; _ → fail }

pi! : String → P ⊤
pi! s = token (ti s)

p[ = token t[
p] = token t]
p: = token t:
p= = token t=
pλ = token tλ
p→ = token t→

paren : ∀ {A} → P A → P A
paren p = p[ *> p <* p]  

{-# NO_TERMINATION_CHECK #-}
pType pType₁ : P Type

pType  = pType₁ +++ _⇒_ <$> pType₁ <* p→ <*> pType
pType₁ = nat <$ pi! "nat" +++ paren pType

apps : Term → List Term → Term
apps f xs = foldl app f xs

mkLet : String → Type → Term → Term → Term
mkLet x a e₁ e₂ = app (lam x a e₂) e₁

mkVar : String → Term
mkVar x = ifYes x == "suc" then suc else var x

{-# NO_TERMINATION_CHECK #-}
pLam pApp pAtom : P Term
pLam =
  pApp
  +++ lam <$ pλ <* p[ <*> pi <* p: <*> pType <* p]
          <*  p→ <*> pLam
  +++ mkLet <$ pi! "let" <*> pi <* p: <*> pType <* p= <*> pLam
            <* pi! "in" <*> pLam

pApp = apps <$> pAtom <*> many pAtom

pAtom =
  mkVar <$> pi  +++
  lit   <$> pn +++
  paren pLam

parseTerm : String → Maybe Term
parseTerm s = parse! pLam (lex s)

-- Examples --

ex₁ = "λ (f : nat → nat) → f (f 4)"
ex₂ = "λ (n : nat) → suc (suc n)"
ex₃ = "(" & ex₂ & ") 5"

ex₄ = "let twice : (nat → nat) → nat → nat
                 = λ (f : nat → nat) -> λ (x : nat) → f (f x) in
       let plustwo : nat → nat
                   = twice suc in
       twice plustwo 15"
