
module AgdaCheatSheet where

open import Prelude

{-

  This file contains simple examples of many of the features of Agda
  and can be used as a reference or to get an overview of what you can
  do. It does not contain any detailed explanations of the features.

 -}

-- Postulates are axioms. Don't use in programs since they
-- will crash if evaluated at run-time. Here they are used
-- just to illustrate the syntax of types.
postulate
  X : Set       -- The type of (small) types is written Set
  T : X → Set  -- Non-dependent function type

  -- Dependent function types (all equivalent)
  f₁ : (x : X) → (y : X) → T x → T y
  f₂ : (x y : X) → T x → T y
  f₃ : (x : X) (y : X) → T x → T y
  f₄ : ∀ x y → T x → T y
  f₅ : (x : X) → ∀ y → T x → T y
  f₆ : ∀ (x : X) y → T x → T y

module ImplicitArguments where
  postulate
    -- Implicit arguments
    g₁ : {x y : X} → T x → T y
    g₂ : ∀ {x y} → T x → T y

  -- Calling functions with implicit arguments.
  h₁ h₂ h₃ : ∀ a b → T a → T b
  h₁ a b t = g₁ t
  h₂ a b t = g₁ {a} {b} t
  h₃ a b t = g₁ {y = b} t

  -- Omitting explicit arguments
  h₄ : ∀ {a b} → T a → T b
  h₄ t = f₁ _ _ t

module DataTypes where

  data L (A : Set) : Set where
    nil  : L A
    cons : A → L A → L A

  -- Indexed data types (indexes go to the right of the colon)
  data V (A : Set) : Nat → Set where
    nil  : V A zero
    cons : ∀ {n} → A → V A n → V A (suc n)

  -- Pattern matching
  append : ∀ {A n m} → V A n → V A m → V A (n + m)
  append nil         ys = ys
  append (cons x xs) ys = cons x (append xs ys)

  data Cmp : Nat → Nat → Set where
    lt : ∀ {n} k → Cmp n (n + suc k)
    eq : ∀ {n}   → Cmp n n
    gt : ∀ {n} k → Cmp (n + suc k) n

  -- Dot patterns: forced by type checking and can contain arbitrary terms
  cmpSuc : ∀ n m → Cmp n m → Cmp (suc n) (suc m)
  cmpSuc n .(n + suc k) (lt k) = lt k
  cmpSuc n .n            eq    = eq
  cmpSuc .(m + suc k) m (gt k) = gt k

  cmp : ∀ n m → Cmp n m
  cmp zero zero = eq
  cmp zero (suc m) = lt m
  cmp (suc n) zero = gt n
  cmp (suc n) (suc m) = cmpSuc n m (cmp n m)

module DefiningSyntax where

  -- Mixfix operators are defined by using '_' in names where
  -- the arguments should go.
  _plus_ : Nat → Nat → Nat
  a plus b = a + b

  infixl 6 _plus_

  maybe′ : {A B : Set} → B → (A → B) → Maybe A → B
  maybe′ = maybe -- from Prelude

  -- You can also declare syntax separate from the name.
  -- This lets you also define syntax for binding constructs.
  syntax maybe′ n (λ x → j) m = if m =just x then j else n

  maybeToList : {A : Set} → Maybe A → List A
  maybeToList m = if m =just x then x ∷ [] else []

  -- Pattern synonyms (can be used both on the left and on the right).
  pattern plus-two n = suc (suc n)

  f : Nat → Nat
  f  0           = 0
  f  1           = 1
  f (plus-two n) = plus-two (f n + f n)

module TermsAndDeclarations where

  -- Let
  times100₁ : Nat → Nat
  times100₁ n =
    let g : Nat → Nat
        g n = n * 10
    in g (g n)

  -- Where
  times100₂ : Nat → Nat
  times100₂ n = g (g n)
    where g : Nat → Nat
          g n = n * 10

  -- Lambda
  times100₃ : Nat → Nat
  times100₃ = λ n → times100₂ n

  -- Pattern matching lambda
  times100₄ : Nat → Nat
  times100₄ = λ { 0 → 0 ; (suc n) → 100 * n + 100 }

  -- Pattern matching lambdas can be used together with case_of_
  -- from the Prelude to simulate case expressions:
  times100₅ : Nat → Nat
  times100₅ n =
    case n of
    λ { 0       → 0
      ; (suc n) → 100 * (n + 1)
      }

module With where

  open DataTypes

  -- The 'with' construct lets you do dependent pattern
  -- matching on arbitrary terms. It adds the term you
  -- want to match on as an extra argument to the current
  -- function. 'With' arguments are separated by bars ('|').
  cmp′ : ∀ n m → Cmp n m
  cmp′ zero zero = eq
  cmp′ zero (suc m) = lt m
  cmp′ (suc n) zero = gt n
  cmp′ (suc n) (suc m)         with cmp′ n m
  cmp′ (suc n) (suc .(n + suc k)) | lt k = lt k
  cmp′ (suc n) (suc .n)           | eq   = eq
  cmp′ (suc .(m + suc k)) (suc m) | gt k = gt k

  -- You use 'with' on more than one term at a time, and if the left
  -- hand side doesn't change you can abbreviate it with ...
  foo : Nat → Nat → Nat
  foo a b with a + b | a - b
  ...        | s     | zero  = s
  ...        | s     | suc d = a + d

  -- The 'rewrite' construct takes an equation u ≡ v and rewrites
  -- u to v in the goal type and context.
  rw : {A : Set} (a b c : Nat) → a + b ≡ 2 * c → Vec A (a + b) → Vec A (2 * c)
  rw a b c prf xs rewrite prf = xs  -- here xs : Vec A (2 * c)

module Modules where

  -- A is a module parameter
  module M (A : Set) where
    f g h : A → A
    f x = x
    g   = f
    h   = f ∘ f
    private  -- Not visible outside M
      i : A → A
      i = g

  open M using  (f) renaming (h to ff; g to f′)
  open M hiding (f)

  -- The functions from M take A as an argument.
  fff : (A : Set) → A → A
  fff A x = f A (ff A x)

  -- Instantiating the module parameters.
  open M Nat using () renaming (f to fn)

  z : Nat
  z = fn 0

module InstanceArguments where
  postulate
    -- Instance arguments (light-weight type classes)
    i : ∀ {x y} {{t : T x}} → T y

  -- Instance arguments are searched for in the context.
  use-i : ∀ {x y} → T x → T y
  use-i tx = i

module Records where

  record M (A : Set) : Set where
    constructor mkR   -- optional
    field
      unit : A
      plus : A → A → A

    -- Additional definitions. Not part of record values.
    sum : List A → A
    sum = foldr plus unit

  MNat : M Nat
  MNat = mkR 0 _+_

  MAnd : M Bool
  MAnd = record { unit = true ; plus = _&&_ }

  module UseM₁ where

    -- Each record defines a module.
    open M  -- brings unit, plus and sum into scope

    plus′ : {A : Set} → M A → A → A → A
    plus′ = plus

    double : ∀ {A} → M A → A → A
    double m x = plus m x x

  module UseM₂ where

    open M {{...}}  -- Instance argument M A instead of explicit

    plus′ : {A : Set} {{_ : M A}} → A → A → A
    plus′ = plus

    double : ∀ {A} {{_ : M A}} → A → A
    double x = plus x x

    six : Nat
    six = sum (1 ∷ 2 ∷ 3 ∷ [])  -- Finds MNat with instance search

module UniversePolymorphism where

  -- There is a hierarchy of universes
  U₀ : Set₁
  U₀ = Set₀  -- same as Set

  U₁ : Set₂
  U₁ = Set₁

  -- and so on ...
  -- Functions (and types) can be polymorphic in the universe level.

  U : (l : Level) → Set (lsuc l)
  U l = Set l
