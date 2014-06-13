
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

lookupAny : ∀ {A} {P Q : A → Set} {xs} → All P xs → Any Q xs → Σ A (λ x → P x × Q x)
lookupAny (p ∷ ps) (zero q) = _ , p , q
lookupAny (p ∷ ps) (suc  i) = lookupAny ps i

lookup∈ : ∀ {A : Set} {P : A → Set} {xs x} → All P xs → x ∈ xs → P x
lookup∈ (p ∷ ps) (zero refl) = p
lookup∈ (p ∷ ps) (suc i)     = lookup∈ ps i

map∈ : ∀ {A B} (f : A → B) {x xs} → x ∈ xs → f x ∈ map f xs
map∈ f (zero refl) = zero refl
map∈ f (suc i)     = suc (map∈ f i)
