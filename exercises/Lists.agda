
module Lists where

open import Prelude

--- All and Any -----------------------------------------------------------

infixr 5 _∷_
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x xs} (p : P x) (ps : All P xs) → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  zero : ∀ {x xs} (p : P x) → Any P (x ∷ xs)
  suc  : ∀ {x xs} (i : Any P xs) → Any P (x ∷ xs)

_∈_ : ∀ {A : Set} → A → List A → Set
x ∈ xs = Any (_≡_ x) xs

-- Three versions of 'all':

-- Using 'case_of_'
all₁ : ∀ {A} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → Maybe (All P xs)
all₁ p [] = just []
all₁ p (x ∷ xs) =
  case p x of
  λ { (yes px) → fmap (_∷_ px) (all₁ p xs)
    ; (no _)   → nothing }

-- Using 'with'
all₂ : ∀ {A} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → Maybe (All P xs)
all₂ p [] = just []
all₂ p (x ∷ xs) with p x
... | yes px = fmap (_∷_ px) (all₂ p xs)
... | no  _  = nothing

-- Using a helper function
private
  -- Use C-c C-h in the hole where you want to use the helper function
  -- to generate the type signature.
  allCons : ∀ {A} {P : A → Set} {x : A} {xs : List A} →
          Dec (P x) → Maybe (All P xs) → Maybe (All P (x ∷ xs))
  allCons (yes px) pxs = _∷_ px <$> pxs
  allCons (no  _)  pxs = nothing

all₃ : ∀ {A} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → Maybe (All P xs)
all₃ p []       = just []
all₃ p (x ∷ xs) = allCons (p x) (all₃ p xs)

-- Exercise: Implement the functions below --

-- Tip: Agda won't allow you to import a module with remaining holes.
--      If you want to use an unfinished function from a different module
--      you can replace it by a postulate:
--        postulate forget∈ : ∀ {A} {x : A} {xs} → x ∈ xs → Nat
--      and comment out the unfinished definition.

forget∈ : ∀ {A} {x : A} {xs} → x ∈ xs → Nat
forget∈ i = {!!}

find : ∀ {A : Set} {{EqA : Eq A}} (x : A) (xs : List A) → Maybe (x ∈ xs)
find x xs = {!!}

lookup∈ : ∀ {A : Set} {P : A → Set} {xs x} → All P xs → x ∈ xs → P x
lookup∈ xs i = {!!}

forgetAll : ∀ {A} {P : A → Set} {xs} → All P xs → List (Σ A P)
forgetAll ps = {!!}

filterMaybe : {A : Set} {P : A → Set} → (∀ x → Maybe (P x)) → List A → List (Σ A P)
filterMaybe p xs = {!!}

--- Path ------------------------------------------------------------------

-- The Path data type represents paths in a graph as a sequence of zero or more
-- edges E i j with source nodes and target nodes matching up domino-style.
data Path {I : Set} (E : I → I → Set) : I → I → Set where
  []  : ∀ {i} → Path E i i
  _∷_ : ∀ {i j k} → E i j → Path E j k → Path E i k

-- Exercise: Solve the following maze.
maze : {E : Nat → Nat → Set} →
       (∀ {n} → E n (2 * n + 1)) →
       (∀ {n} → E n (n div 3)) →
       Path E 9 10
maze up dn = {!!}

-- Exercise: Implement map and join.
mapPath : ∀ {I} {E₁ E₂ : I → I → Set} {f : I → I} (g : ∀ {i j} → E₁ i j → E₂ (f i) (f j)) →
      ∀ {i j} → Path E₁ i j → Path E₂ (f i) (f j)
mapPath g xs = {!!}

joinPath : ∀ {I} {E : I → I → Set} {i j k} → Path E i j → Path E j k → Path E i k
joinPath xs ys = {!!}
