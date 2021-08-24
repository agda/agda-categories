{-# OPTIONS --without-K --safe #-}
module Categories.Category.Unbundled where

-- This is basically identical to Category, except that the
-- Obj type is a parameter rather than a field.

open import Level
open import Function.Base using (flip)

open import Relation.Binary using (Rel; IsEquivalence)

record Category {o : Level} (Obj : Set o) (ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  eta-equality
  infix  4 _≈_ _⇒_
  infixr 9 _∘_

  field
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
