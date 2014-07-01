
open import Prelude

main : IO Unit
main = putStrLn "Hello World!"

data Type : Set where
  nat bool : Type

Cxt = List Type

infix 3 _∈_
data Any {A : Set} (P : A → Set) : List A → Set where
  zero : ∀ {x xs} → P x → Any P (x ∷ xs)
  suc  : ∀ {y xs} → Any P xs → Any P (y ∷ xs)

_∈_ : ∀ {A} x (xs : List A) → Set
_∈_ = Any ∘ _≡_

data Expr (Γ : Cxt) : Type → Set where
  var    : ∀ {a} → a ∈ Γ → Expr Γ a
  lit    : Nat → Expr Γ nat
  true false : Expr Γ bool
  plus   : Expr Γ nat → Expr Γ nat → Expr Γ nat
  if     : ∀ {a} → Expr Γ bool → Expr Γ a → Expr Γ a → Expr Γ a
  iszero : Expr Γ nat → Expr Γ bool

Value : Type → Set
Value nat = Nat
Value bool = Bool

infixr 5 _∷_
data All {A : Set} (T : A → Set) : List A → Set where
  [] : All T []
  _∷_ : ∀ {x xs} → T x → All T xs → All T (x ∷ xs)

Env : Cxt → Set
Env Γ = All Value Γ

lookupVar : ∀ {Γ a} → All Value Γ → a ∈ Γ → Value a
lookupVar (x ∷ xs₁) (zero refl) = x
lookupVar (x ∷ xs) (suc i) = lookupVar xs i

eval : ∀ {Γ a} → Env Γ → Expr Γ a → Value a
eval env (var i) = lookupVar env i
eval env (lit x) = x
eval env true = true
eval env false = false
eval env (plus e e₁) = eval env e + eval env e₁
eval env (if e e₁ e₂) = if eval env e then eval env e₁ else eval env e₂
eval env (iszero e) = if isYes (eval env e == 0) then true else false

all : ∀ {A} {P : A → Set} → (∀ x → Maybe (P x)) → ∀ xs → Maybe (All P xs)
all p []       = pure []
all p (x ∷ xs) = _∷_ <$> p x <*> all p xs
  -- case p x of
  -- λ { nothing → nothing
  --   ; (just px) → _∷_ px <$> all p xs }
