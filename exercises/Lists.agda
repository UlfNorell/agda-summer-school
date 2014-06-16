
open import Prelude

infixr 5 _∷_
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x xs} (p : P x) (ps : All P xs) → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  zero : ∀ {x xs} (p : P x) → Any P (x ∷ xs)
  suc  : ∀ {x xs} (i : Any P xs) → Any P (x ∷ xs)

_∈_ : ∀ {A : Set} → A → List A → Set
x ∈ xs = Any (_≡_ x) xs

-- Exercise: Implement the functions below --

postulate
  elem : ∀ {A : Set} {{EqA : Eq A}} (x : A) (xs : List A) → Maybe (x ∈ xs)

  lookup∈ : ∀ {A : Set} {P : A → Set} {xs x} → All P xs → x ∈ xs → P x

  forgetAll : ∀ {A} {P : A → Set} {xs} → All P xs → List (Σ A P)

  allOrAny : ∀ {A} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → Either (Any (¬_ ∘ P) xs) (All P xs)

  lookupAny : ∀ {A} {P Q : A → Set} {xs} → All P xs → Any Q xs → Σ A (λ x → P x × Q x)

  map∈ : ∀ {A B} (f : A → B) {x xs} → x ∈ xs → f x ∈ map f xs


-- Exercise: Define a data type Path, representing a sequence of zero or more edges
-- E i j where the second index of one edge matches the first index of the next. For
-- instance, if you have E : Nat → Nat → Set and a : E 0 1, b : E 1 5, and c : E 5 2
-- you should be able to represent the sequence of a, b, and c as an element of
-- Path E 0 2.
data Path {I : Set} (E : I → I → Set) : I → I → Set where

mapPath : ∀ {I} {E₁ E₂ : I → I → Set} {f : I → I} (g : ∀ {i j} → E₁ i j → E₂ (f i) (f j)) →
      ∀ {i j} → Path E₁ i j → Path E₂ (f i) (f j)
mapPath g ()

_>+>_ : ∀ {I} {E : I → I → Set} {i j k} → Path E i j → Path E j k → Path E i k
() >+> ()

-- TODO: Example Paths
