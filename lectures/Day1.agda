
open import Prelude

data Type : Set where
  nat : Type
  bool : Type

Cxt = List Type

infix 3 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  zero : ∀ {xs} → x ∈ x ∷ xs
  suc  : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

data Expr (Γ : Cxt) : Type → Set where
  var   : ∀ {a} → a ∈ Γ → Expr Γ a
  lit   : (n : Nat) → Expr Γ nat
  true  : Expr Γ bool
  false : Expr Γ bool
  less  : (a b : Expr Γ nat) → Expr Γ bool
  plus  : (a b : Expr Γ nat) → Expr Γ nat
  if    : ∀ {t} (a : Expr Γ bool) (b c : Expr Γ t) → Expr Γ t

Value : Type → Set
Value nat = Nat
Value bool = Bool

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  zero : ∀ {x xs} → P x → Any P (x ∷ xs)
  suc  : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

_∈′_ : {A : Set} (x : A) → List A → Set
x ∈′ xs = Any (λ y → x ≡ y) xs

lookup∈ : ∀ {A} {P : A → Set} {x xs} → All P xs → x ∈ xs → P x
lookup∈ (p ∷ ps) zero = p
lookup∈ (p ∷ ps) (suc i) = lookup∈ ps i

Env : Cxt → Set
Env Γ = All Value Γ

eval : ∀ {Γ t} → Env Γ → Expr Γ t → Value t
eval env (var x) = lookup∈ env x
eval env (lit n) = n
eval env true = true
eval env false = false
eval env (less e e₁) = eval env e < eval env e₁
eval env (plus e e₁) = eval env e + eval env e₁
eval env (if e e₁ e₂) = if eval env e then eval env e₁ else eval env e₂

Γ : Cxt
Γ = nat ∷ bool ∷ []

env : Env Γ
env = 5 ∷ false ∷ []

e : Expr Γ nat
e = if (var (suc zero)) (var zero) (plus (lit 4) (var zero))
