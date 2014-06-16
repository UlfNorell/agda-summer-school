
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

elem : ∀ {A : Set} {{EqA : Eq A}} (x : A) (xs : List A) → Maybe (x ∈ xs)
elem x [] = nothing
elem x (y ∷ xs) with x == y
... | yes eq = just (zero eq)
... | no  _  = suc <$> elem x xs 

lookup∈ : ∀ {A : Set} {P : A → Set} {xs x} → All P xs → x ∈ xs → P x
lookup∈ (p ∷ ps) (zero refl) = p
lookup∈ (p ∷ ps) (suc i)     = lookup∈ ps i

forgetAll : ∀ {A} {P : A → Set} {xs} → All P xs → List (Σ A P)
forgetAll [] = []
forgetAll (p ∷ ps) = (_ , p) ∷ forgetAll ps

allOrAny : ∀ {A} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → Either (Any (¬_ ∘ P) xs) (All P xs)
allOrAny p [] = right []
allOrAny p (x ∷ xs) with p x
... | yes px = either (left ∘ suc) (right ∘ _∷_ px) (allOrAny p xs)
... | no npx = left (zero npx)

lookupAny : ∀ {A} {P Q : A → Set} {xs} → All P xs → Any Q xs → Σ A (λ x → P x × Q x)
lookupAny (p ∷ ps) (zero q) = _ , p , q
lookupAny (p ∷ ps) (suc  i) = lookupAny ps i

map∈ : ∀ {A B} (f : A → B) {x xs} → x ∈ xs → f x ∈ map f xs
map∈ f (zero refl) = zero refl
map∈ f (suc i)     = suc (map∈ f i)



-- Exercise: Define a data type Path, representing a sequence of zero or more edges
-- E i j where the second index of one edge matches the first index of the next. For
-- instance, if you have E : Nat → Nat → Set and a : E 0 1, b : E 1 5, and c : E 5 2
-- you should be able to represent the sequence of a, b, and c as an element of
-- Path E 0 2.
data Path {I : Set} (E : I → I → Set) : I → I → Set where
  []  : ∀ {i} → Path E i i
  _∷_ : ∀ {i j k} → E i j → Path E j k → Path E i k

mapPath : ∀ {I} {E₁ E₂ : I → I → Set} {f : I → I} (g : ∀ {i j} → E₁ i j → E₂ (f i) (f j)) →
      ∀ {i j} → Path E₁ i j → Path E₂ (f i) (f j)
mapPath g [] = []
mapPath g (x ∷ xs) = g x ∷ mapPath g xs

_>+>_ : ∀ {I} {E : I → I → Set} {i j k} → Path E i j → Path E j k → Path E i k
[]       >+> ys = ys
(x ∷ xs) >+> ys = x ∷ (xs >+> ys)
