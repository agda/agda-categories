{-# OPTIONS --without-K --safe #-}
module Categories.Category.Core where

open import Level
open import Function using (flip)

open import Relation.Binary hiding (_⇒_)
import Relation.Binary.Reasoning.Setoid as SetoidR

-- Basic definition of a |Category| with a Hom setoid.
-- Also comes with some reasoning combinators (see HomReasoning)
record Category (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix  4 _≈_ _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Rel Obj ℓ
    _≈_ : ∀ {A B} → Rel (A ⇒ B) e

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    equiv     : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

  module Equiv {A B : Obj} = IsEquivalence (equiv {A} {B})

  open Equiv

  dom : ∀ {A B} → (A ⇒ B) → Obj
  dom {A} _ = A

  cod : ∀ {A B} → (A ⇒ B) → Obj
  cod {B = B} _ = B

  ∘-resp-≈ˡ : ∀ {A B C} {f h : B ⇒ C} {g : A ⇒ B} → f ≈ h → f ∘ g ≈ h ∘ g
  ∘-resp-≈ˡ pf = ∘-resp-≈ pf refl

  ∘-resp-≈ʳ : ∀ {A B C} {f h : A ⇒ B} {g : B ⇒ C} → f ≈ h → g ∘ f ≈ g ∘ h
  ∘-resp-≈ʳ pf = ∘-resp-≈ refl pf

  hom-setoid : ∀ {A B} → Setoid _ _
  hom-setoid {A} {B} = record
    { Carrier       = A ⇒ B
    ; _≈_           = _≈_
    ; isEquivalence = equiv
    }

  -- Reasoning combinators.  _≈⟨_⟩_ and _≈˘⟨_⟩_ from SetoidR.
  -- Also some useful combinators for doing reasoning on _∘_ chains
  module HomReasoning {A B : Obj} where
    open SetoidR (hom-setoid {A} {B}) public
    open Equiv {A = A} {B = B} public

    infixr 4 _⟩∘⟨_ refl⟩∘⟨_ _⟩∘⟨refl
    _⟩∘⟨_ : ∀ {M} {f h : M ⇒ B} {g i : A ⇒ M} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i
    _⟩∘⟨_ = ∘-resp-≈

    refl⟩∘⟨_ : ∀ {M} {f : M ⇒ B} {g i : A ⇒ M} → g ≈ i → f ∘ g ≈ f ∘ i
    refl⟩∘⟨_ = Equiv.refl ⟩∘⟨_

    _⟩∘⟨refl : ∀ {M} {f h : M ⇒ B} {g : A ⇒ M} → f ≈ h → f ∘ g ≈ h ∘ g
    _⟩∘⟨refl = _⟩∘⟨ Equiv.refl

    -- convenient inline versions
    infix 2 ⟺
    infixr 3 _○_
    ⟺ : {f g : A ⇒ B} → f ≈ g → g ≈ f
    ⟺ = Equiv.sym
    _○_ : {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
    _○_ = Equiv.trans

  -- Combinators for commutative diagram
  -- The idea is to use the combinators to write commutations in a more readable way.
  -- It starts with [_⇒_]⟨_≈_⟩, and within the third and forth places, use _⇒⟨_⟩_ to
  -- connect morphisms with the intermediate object specified.
  module Commutation where
    infix 1 [_⇒_]⟨_≈_⟩
    [_⇒_]⟨_≈_⟩ : ∀ (A B : Obj) → A ⇒ B → A ⇒ B → Set _
    [ A ⇒ B ]⟨ f ≈ g ⟩ = f ≈ g

    infixl 2 connect
    connect : ∀ {A C : Obj} (B : Obj) → A ⇒ B → B ⇒ C → A ⇒ C
    connect B f g = g ∘ f

    syntax connect B f g = f ⇒⟨ B ⟩ g

  op : Category o ℓ e
  op = record
    { Obj = Obj
    ; _⇒_ = flip _⇒_
    ; _≈_ = _≈_
    ; _∘_ = flip _∘_
    ; id = id
    ; assoc = sym assoc
    ; identityˡ = identityʳ
    ; identityʳ = identityˡ
    ; equiv = equiv
    ; ∘-resp-≈ = flip ∘-resp-≈
    }

  -- Q: Should the following 3 really be defined here?
  CommutativeSquare : ∀ {A B C D} → (f : A ⇒ B) (g : A ⇒ C) (h : B ⇒ D) (i : C ⇒ D) → Set _
  CommutativeSquare f g h i = h ∘ f ≈ i ∘ g

  {- Locally open equational reasoning module for clearer proofs. -}
  module _ {A B : Obj} where
    open HomReasoning {A} {B} public

  id-unique : ∀ {o} {f : o ⇒ o} → (∀ g → g ∘ f ≈ g) → f ≈ id
  id-unique {o} {f} g∘f≈g = begin
      f
    ≈˘⟨ identityˡ ⟩
      id ∘ f
    ≈⟨ g∘f≈g id ⟩
      id
    ∎

  id-comm : ∀ {a b} {f : a ⇒ b} → f ∘ id ≈ id ∘ f
  id-comm {a} {b} {f} = begin
      f ∘ id
    ≈⟨ identityʳ ⟩
      f
    ≈˘⟨ identityˡ ⟩
      id ∘ f
    ∎

  id-idemp : ∀ {a} → id {a} ∘ id ≈ id
  id-idemp = identityʳ
