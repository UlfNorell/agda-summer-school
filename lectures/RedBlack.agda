
open import Prelude

module RedBlack {A : Set} {{OrdA : Ord A}} where

record Prf (A : Set) : Set where
  constructor !
  field
    {{prf}} : A

data Bound : Set where
  -∞ ∞ : Bound
  # : A → Bound

LessBound : Bound → Bound → Set
LessBound ∞ _ = ⊥
LessBound _ ∞ = ⊤
LessBound _ -∞ = ⊥
LessBound -∞ _ = ⊤
LessBound (# x) (# y) = LessThan x y

OrdBound : Ord Bound
OrdBound = record { LessThan = LessBound ; compare = cmpBound }
  where
    cmpBound : ∀ x y → Comparison LessBound x y
    cmpBound -∞ -∞ = equal refl
    cmpBound -∞ ∞ = less _
    cmpBound -∞ (# x) = less _
    cmpBound ∞ -∞ = greater tt
    cmpBound ∞ ∞ = equal refl
    cmpBound ∞ (# x) = greater tt
    cmpBound (# x) -∞ = greater tt
    cmpBound (# x) ∞ = less tt
    cmpBound (# x) (# y) with compare x y
    ... | less lt = less lt
    ... | greater gt = greater gt
    cmpBound (# x) (# .x) | equal refl = equal refl

Bounds = Bound × Bound

Rel = Bounds → Set

PrfR : Rel → Rel
PrfR R b = Prf (R b)

data _∧_ (S T : Rel) : Rel where
  pivot : ∀ {l u} p → S (l , # p) → T (# p , u) → (S ∧ T) (l , u)

pattern -⟨_⟩- p = pivot p ! !
pattern _⟨_⟩_ l p r = pivot p l r

Less : Rel
Less = PrfR (uncurry LessThan)

Bounded : Rel
Bounded = Less ∧ Less

data Color : Set where
  red black : Color

data Tree′ (b : Bounds) : Nat → Color → Set

Tree : Nat → Color → Rel
Tree n c b = Tree′ b n c

data Tree′ b where
  leaf′  : Less b → Tree 0 black b
  red   : ∀ {n} → (Tree n black ∧ Tree n black) b → Tree n red b
  black : ∀ {c₁ c₂ n} → (Tree n c₁ ∧ Tree n c₂) b → Tree (suc n) black b

pattern leaf = leaf′ !

data PreTree′ (b : Bounds) (n : Nat) : Color → Set

PreTree : Nat → Color → Bounds → Set
PreTree n c b = PreTree′ b n c

data PreTree′ b n where
  red         : ∀ {c₁ c₂} → (Tree n c₁ ∧ Tree n c₂) b → PreTree n red b
  maybe-black : ∀ {c} → Tree n c b → PreTree n black b

pattern _b⟨_⟩_   l x r = black (l ⟨ x ⟩ r)
pattern _r⟨_⟩_   l x r = red (l ⟨ x ⟩ r)
pattern _pb⟨_⟩_  l x r = maybe-black (black (l ⟨ x ⟩ r))
pattern _pbr⟨_⟩_ l x r = maybe-black (red   (l ⟨ x ⟩ r))
pattern _rbb⟨_⟩_ l x r = red {c₁ = black} {c₂ = black} (l ⟨ x ⟩ r)

balance-l : ∀ {b c₁ c₂ n} →
            (PreTree n c₁ ∧ Tree n c₂) b →
            PreTree (suc n) black b
balance-l (((l₁ r⟨ z ⟩ l₂) r⟨ x ⟩ l₃) ⟨ y ⟩ r) =
  (l₁ b⟨ z ⟩ l₂) pbr⟨ x ⟩ (l₃ b⟨ y ⟩ r)
balance-l ((l₁ r⟨ z ⟩ (l₂ r⟨ x ⟩ l₃)) ⟨ y ⟩ r) =
  (l₁ b⟨ z ⟩ l₂) pbr⟨ x ⟩ (l₃ b⟨ y ⟩ r)
balance-l ((l₁ rbb⟨ x ⟩ l₂) ⟨ y ⟩ r) =
  (l₁ r⟨ x ⟩ l₂) pb⟨ y ⟩ r
balance-l (maybe-black l ⟨ y ⟩ r) = l pb⟨ y ⟩ r

balance-r : ∀ {b c₁ c₂ n} →
            (Tree n c₁ ∧ PreTree n c₂) b →
            PreTree (suc n) black b
balance-r (l ⟨ y ⟩ ((r₁ r⟨ z ⟩ r₂) r⟨ x ⟩ r₃)) =
  (l b⟨ y ⟩ r₁) pbr⟨ z ⟩ (r₂ b⟨ x ⟩ r₃)
balance-r (l ⟨ y ⟩ (r₁ r⟨ x ⟩ (r₂ r⟨ z ⟩ r₃))) =
  (l b⟨ y ⟩ r₁) pbr⟨ x ⟩ (r₂ b⟨ z ⟩ r₃)
balance-r (l ⟨ y ⟩ (r₁ rbb⟨ x ⟩ r₂)) =
  l pb⟨ y ⟩ (r₁ r⟨ x ⟩ r₂)
balance-r (l ⟨ y ⟩ maybe-black r) = l pb⟨ y ⟩ r

ins : ∀ {b c n} → Bounded b → Tree n c b → PreTree n c b
ins -⟨ x ⟩- leaf = leaf pbr⟨ x ⟩ leaf
ins -⟨ x ⟩- (red (l ⟨ y ⟩ r)) =
  case compare x y of
  λ { (less _)    → case ins -⟨ x ⟩- l of λ { (maybe-black l′) → l′ r⟨ y ⟩ r }
    ; (greater _) → case ins -⟨ x ⟩- r of λ { (maybe-black r′) → l r⟨ y ⟩ r′ }
    ; (equal _)   → l r⟨ y ⟩ r
    }
ins -⟨ x ⟩- (black (l ⟨ y ⟩ r)) =
  case compare x y of
  λ { (less _)    → balance-l (ins -⟨ x ⟩- l ⟨ y ⟩ r)
    ; (greater _) → balance-r (l ⟨ y ⟩ ins -⟨ x ⟩- r)
    ; (equal _)   → l pb⟨ y ⟩ r }

data RedBlackTree : Set where
  mkT : ∀ {n} → Tree n black (-∞ , ∞) → RedBlackTree

insert : A → RedBlackTree → RedBlackTree
insert x (mkT t) with ins -⟨ x ⟩- t
... | l pbr⟨ y ⟩ r      = mkT $ l b⟨ y ⟩ r
... | l  pb⟨ y ⟩ r      = mkT $ l b⟨ y ⟩ r
... | maybe-black leaf = mkT leaf
