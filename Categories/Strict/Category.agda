{-# OPTIONS --without-K --safe #-}
module Categories.Strict.Category where

-- like a Category, but ≈ is baked in to be ≡
-- This is the closest approximation to a Strict category in MLTT
--   Here there is no use of ≡ on objects, but there is in Functor
open import Level

open import Function using (flip)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; setoid; isEquivalence; cong₂)
import Relation.Binary.Reasoning.Setoid as SetoidR
import Categories.Category as Cat

-- Definition of a |Category| with 'strict' equality on Hom
-- Also comes with some reasoning combinators (see HomReasoning)
record Category (o ℓ : Level) : Set (suc (o ⊔ ℓ)) where
  eta-equality
  infix  4 _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Rel Obj ℓ

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f

  dom : ∀ {A B} → (A ⇒ B) → Obj
  dom {A} _ = A

  cod : ∀ {A B} → (A ⇒ B) → Obj
  cod {B = B} _ = B

  -- Reasoning combinators.  _≈⟨_⟩_ and _≈˘⟨_⟩_ from SetoidR.
  -- Also some useful combinators for doing reasoning on _∘_ chains
  module HomReasoning {A B : Obj} where
    open SetoidR (setoid (A ⇒ B)) public

    infixr 4 _⟩∘⟨_ refl⟩∘⟨_ _⟩∘⟨refl
    _⟩∘⟨_ : ∀ {M} {f h : M ⇒ B} {g i : A ⇒ M} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i
    _⟩∘⟨_ = cong₂ _∘_

    refl⟩∘⟨_ : ∀ {M} {f : M ⇒ B} {g i : A ⇒ M} → g ≡ i → f ∘ g ≡ f ∘ i
    refl⟩∘⟨ refl = refl

    _⟩∘⟨refl : ∀ {M} {f h : M ⇒ B} {g : A ⇒ M} → f ≡ h → f ∘ g ≡ h ∘ g
    _⟩∘⟨refl = _⟩∘⟨ refl
    -- convenient inline versions
    infix 2 ⟺
    infixr 3 _○_
    ⟺ : {f g : A ⇒ B} → f ≡ g → g ≡ f
    ⟺ = sym
    _○_ : {f g h : A ⇒ B} → f ≡ g → g ≡ h → f ≡ h
    _○_ = trans

  -- Combinators for commutative diagram
  -- The idea is to use the combinators to write commutations in a more readable way.
  -- It starts with [_⇒_]⟨_≈_⟩, and within the third and forth places, use _⇒⟨_⟩_ to
  -- connect morphisms with the intermediate object specified.
  module Commutation where
    infix 1 [_⇒_]⟨_≡_⟩
    [_⇒_]⟨_≡_⟩ : ∀ (A B : Obj) → A ⇒ B → A ⇒ B → Set _
    [ A ⇒ B ]⟨ f ≡ g ⟩ = f ≡ g

    infixl 2 connect
    connect : ∀ {A C : Obj} (B : Obj) → A ⇒ B → B ⇒ C → A ⇒ C
    connect B f g = g ∘ f

    syntax connect B f g = f ⇒⟨ B ⟩ g

  op : Category o ℓ
  op = record
    { Obj = Obj
    ; _⇒_ = flip _⇒_
    ; _∘_ = flip _∘_
    ; id = id
    ; assoc = sym assoc
    ; identityˡ = identityʳ
    ; identityʳ = identityˡ
    }

  -- Q: Should the following 3 really be defined here?
  CommutativeSquare : ∀ {A B C D} → (f : A ⇒ B) (g : A ⇒ C) (h : B ⇒ D) (i : C ⇒ D) → Set _
  CommutativeSquare f g h i = h ∘ f ≡ i ∘ g

  id-unique : ∀ {o} {f : o ⇒ o} → (∀ g → g ∘ f ≡ g) → f ≡ id
  id-unique g∘f≈g = trans (sym identityˡ) (g∘f≈g id)

  id-comm : ∀ {a b} {f : a ⇒ b} → f ∘ id ≡ id ∘ f
  id-comm = trans identityʳ (sym identityˡ)

StrictCat⇒Cat : {o ℓ : Level} → (P : Category o ℓ) → Cat.Category o ℓ ℓ
StrictCat⇒Cat P = record
  { Obj = Obj
  ; _⇒_ = _⇒_
  ; _≈_ = _≡_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv = isEquivalence
  ; ∘-resp-≈ = cong₂ _∘_
  }
  where open Category P

infix 10  _[_,_] _[_∘_]

_[_,_] : ∀ {o ℓ} → (C : Category o ℓ) → (X : Category.Obj C) → (Y : Category.Obj C) → Set ℓ
_[_,_] = Category._⇒_

_[_∘_] : ∀ {o ℓ} → (C : Category o ℓ) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
_[_∘_] = Category._∘_
