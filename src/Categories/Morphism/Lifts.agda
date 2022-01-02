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

record Lifts {A B X Y} (i : A ⇒ B) (p : X ⇒ Y) : Set (ℓ ⊔ e) where
  field
    -- The diagonal filler of a given commutative square. Note that this
    -- isn't required to be unique.
    filler : ∀ {f : A ⇒ X} {g : B ⇒ Y} → CommutativeSquare i f g p → B ⇒ X
    -- The "left" triangle of the diagram must commute.
    fill-commˡ : ∀ {f g} → (sq : CommutativeSquare i f g p) → filler sq ∘ i ≈ f
    -- The "right" triangle of the diagram must commute.
    fill-commʳ : ∀ {f g} → (sq : CommutativeSquare i f g p) → p ∘ filler sq ≈ g

-- We often want to discuss lifting properties with respect to /classes/ of morphisms,
-- not just individual morphisms.

-- Shorthand for denoting a class of morphisms.
MorphismClass : (p : Level) → Set (o ⊔ ℓ ⊔ suc p)
MorphismClass p = ∀ {X Y} → X ⇒ Y → Set p

-- A morphisms has the left lifting property with respect to a class of morphisms 'P'
-- if it has the left lifting property with each element of 'P'.
LeftLifts : ∀ {p} {A B} → (i : A ⇒ B) → MorphismClass p → Set (o ⊔ ℓ ⊔ e ⊔ p)
LeftLifts i P = ∀ {X Y} → (f : X ⇒ Y) → P f → Lifts i f

-- The situation is analogous for right lifting properties.
RightLifts : ∀ {p} {A B} → (i : A ⇒ B) → MorphismClass p → Set (o ⊔ ℓ ⊔ e ⊔ p)
RightLifts i P = ∀ {X Y} → (f : X ⇒ Y) → P f → Lifts f i
