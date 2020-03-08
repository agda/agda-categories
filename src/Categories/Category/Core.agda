{-# OPTIONS --without-K --safe #-}
module Categories.Category.Core where

open import Level
open import Function using (flip)

open import Relation.Binary hiding (_⇒_)
import Relation.Binary.PropositionalEquality as ≡
import Relation.Binary.Reasoning.Setoid as SetoidR

-- Basic definition of a |Category| with a Hom setoid.
-- Also comes with some reasoning combinators (see HomReasoning)
record Category (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  eta-equality
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
    -- We add a symmetric proof of associativity so that the opposite category of the
    -- opposite category is definitionally equal to the original category. See how
    -- `op` is implemented.
    sym-assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    -- We add a proof of "neutral" identity proof, in order to ensure the opposite of
    -- constant functor is definitionally equal to itself.
    identity² : ∀ {A} → id ∘ id {A} ≈ id {A}
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

    infixr 4 _⟩∘⟨_ refl⟩∘⟨_
    infixl 5 _⟩∘⟨refl
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

    -- for reasoning in the Strict cases
    ≡⇒≈ : {f g : A ⇒ B} → f ≡.≡ g → f ≈ g
    ≡⇒≈ ≡.refl = Equiv.refl

    subst₂≈ : {C D : Obj} {f g : A ⇒ B} → f ≈ g → (eq₁ : A ≡.≡ C) (eq₂ : B ≡.≡ D) →
      ≡.subst₂ (_⇒_) eq₁ eq₂ f ≈ ≡.subst₂ (_⇒_) eq₁ eq₂ g
    subst₂≈ f≈g ≡.refl ≡.refl = f≈g

  -- Combinators for commutative diagram
  -- The idea is to use the combinators to write commutations in a more readable way.
  -- It starts with [_⇒_]⟨_≈_⟩, and within the third and fourth places, use _⇒⟨_⟩_ to
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
    { Obj       = Obj
    ; _⇒_       = flip _⇒_
    ; _≈_       = _≈_
    ; _∘_       = flip _∘_
    ; id        = id
    ; assoc     = sym-assoc
    ; sym-assoc = assoc
    ; identityˡ = identityʳ
    ; identityʳ = identityˡ
    ; identity² = identity²
    ; equiv     = equiv
    ; ∘-resp-≈  = flip ∘-resp-≈
    }

  -- Q: Should this really be defined here?
  CommutativeSquare : ∀ {A B C D} → (f : A ⇒ B) (g : A ⇒ C) (h : B ⇒ D) (i : C ⇒ D) → Set _
  CommutativeSquare f g h i = h ∘ f ≈ i ∘ g

-- Since we add extra proofs in the definition of `Category` (i.e. `sym-assoc` and
-- `identity²`), we might still want to construct a `Category` in its originally
-- easier manner. Thus, this redundant definition is here to ease the construction.
record CategoryHelper (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
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

categoryHelper : ∀ {o ℓ e} → CategoryHelper o ℓ e → Category o ℓ e
categoryHelper C = record
  { Obj       = Obj
  ; _⇒_       = _⇒_
  ; _≈_       = _≈_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = assoc
  ; sym-assoc = sym assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identityˡ
  ; equiv     = equiv
  ; ∘-resp-≈  = ∘-resp-≈
  }
  where open CategoryHelper C
        module _ {A B} where
          open IsEquivalence (equiv {A} {B}) public
