{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- Lifting Properties
module Categories.Morphism.Lifts {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open Category 𝒞
open Definitions 𝒞

-- A pair of morphisms has the lifting property if every commutative
-- square admits a diagonal filler. We say that 'i' has the left lifting
-- property with respect to 'p', and that 'p' has the right lifting property
-- with respect to 'i'.
--
-- Graphically, the situation is as follows:
--
--      f
--   A ────> X
--   │     ^ │
--   │  ∃ ╱  │
-- i │   ╱   │ p
--   │  ╱    │
--   V ╱     V
--   B ────> Y
--      g
--
-- Note that the filler is /not/ required to be unique.
--
-- For ease of use, we define lifts in two steps:
-- * 'Filler' describes the data required to fill a /particular/ commutative square.
-- * 'Lifts' then quantifies over all commutative squares.

record Filler {A B X Y} {i : A ⇒ B} {f : A ⇒ X} {g : B ⇒ Y} {p : X ⇒ Y}
              (comm : CommutativeSquare i f g p) : Set (ℓ ⊔ e) where
  field
    filler : B ⇒ X
    fill-commˡ : filler ∘ i ≈ f
    fill-commʳ : p ∘ filler ≈ g

Lifts : ∀ {A B X Y} → (i : A ⇒ B) → (p : X ⇒ Y) → Set (ℓ ⊔ e)
Lifts i p = ∀ {f g} → (comm : CommutativeSquare i f g p) → Filler comm

--------------------------------------------------------------------------------
-- Lifings of Morphism Classes

-- Shorthand for denoting a class of morphisms.
MorphismClass : (p : Level) → Set (o ⊔ ℓ ⊔ suc p)
MorphismClass p = ∀ {X Y} → X ⇒ Y → Set p

-- A morphism 'i' is called "projective" with respect to some morphism class 'J'
-- if it has the left-lifting property against every element of 'J'.
Projective : ∀ {j} {A B} → MorphismClass j → (i : A ⇒ B) → Set (o ⊔ ℓ ⊔ e ⊔ j)
Projective J i = ∀ {X Y} → (f : X ⇒ Y) → J f → Lifts i f

-- Dually, a morphism 'i' is called "injective" with repsect to a morphism class 'J'
-- if it has the right-lifting property against every element of 'J'.
Injective : ∀ {j} {A B} → MorphismClass j → (i : A ⇒ B) → Set (o ⊔ ℓ ⊔ e ⊔ j)
Injective J i = ∀ {X Y} → (f : X ⇒ Y) → J f → Lifts f i

-- The class of J-Projective morphisms.
Proj : ∀ {j} (J : MorphismClass j) → MorphismClass (o ⊔ ℓ ⊔ e ⊔ j)
Proj J = Projective J

-- The class of J-Injective morphisms.
Inj : ∀ {j} (J : MorphismClass j) → MorphismClass (o ⊔ ℓ ⊔ e ⊔ j)
Inj J = Injective J
