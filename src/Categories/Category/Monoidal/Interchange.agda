{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)

-- The "four middle interchange" for monoidal categories.
--
-- Aka the "interchange law" or "exchange law" (though those terms are
-- more comonly used in the more general context of composition in
-- 2-categories).

module Categories.Category.Monoidal.Interchange
  {o ℓ e} {C : Category o ℓ e} where

open import Level using (_⊔_)

import Categories.Category.Monoidal.Construction.Product as MonoidalProduct
open import Categories.Category.Monoidal.Core using (Monoidal)
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper)
open import Categories.Morphism C using (_≅_; module ≅)

open Category C using (Obj; id; _⇒_; _∘_; _≈_)
open Commutation C

private
  variable
    W W₁ W₂ X X₁ X₂ Y Y₁ Y₂ Z Z₁ Z₂ : Obj
    f g h i : X ⇒ Y

-- An abstract definition of an interchange map with the minimal set
-- of coherence laws required to make the tensor product ⊗ of C a
-- monoidal functor.  (See also Categories.Functor.Monoidal.Tensor.)

record HasInterchange (M : Monoidal C) : Set (o ⊔ ℓ ⊔ e) where
  open Monoidal M using (_⊗₀_; _⊗₁_; unit; ⊗)
  open MonoidalUtilities.Shorthands M using (α⇒; λ⇐; λ⇒; ρ⇒)

  -- The "four middle interchange" for tensor products.

  field swapInner : ∀ {W X Y Z} → (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ≅ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z)

  module swapInner {W X Y Z} = _≅_ (swapInner {W} {X} {Y} {Z})
  private
    i⇒ = swapInner.from
    i⇐ = swapInner.to

  -- Naturality and coherence laws of the interchange.

  field
    natural : i⇒ ∘ (f ⊗₁ g) ⊗₁ (h ⊗₁ i) ≈ (f ⊗₁ h) ⊗₁ (g ⊗₁ i) ∘ i⇒

    assoc : [ ((X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂)) ⊗₀ (Z₁ ⊗₀ Z₂) ⇒
              (X₁ ⊗₀ (Y₁ ⊗₀ Z₁)) ⊗₀ (X₂ ⊗₀ (Y₂ ⊗₀ Z₂)) ]⟨
              i⇒ ⊗₁ id   ⇒⟨ ((X₁ ⊗₀ Y₁) ⊗₀ (X₂ ⊗₀ Y₂)) ⊗₀ (Z₁ ⊗₀ Z₂) ⟩
              i⇒         ⇒⟨ ((X₁ ⊗₀ Y₁) ⊗₀ Z₁) ⊗₀ ((X₂ ⊗₀ Y₂) ⊗₀ Z₂) ⟩
              α⇒ ⊗₁ α⇒
            ≈ α⇒         ⇒⟨ (X₁ ⊗₀ X₂) ⊗₀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⟩
              id ⊗₁ i⇒   ⇒⟨ (X₁ ⊗₀ X₂) ⊗₀ ((Y₁ ⊗₀ Z₁) ⊗₀ (Y₂ ⊗₀ Z₂)) ⟩
              i⇒
            ⟩

    unitˡ : [ unit ⊗₀ (X ⊗₀ Y) ⇒ (X ⊗₀ Y) ]⟨
              λ⇐ ⊗₁ id   ⇒⟨ (unit ⊗₀ unit) ⊗₀ (X ⊗₀ Y) ⟩
              i⇒         ⇒⟨ (unit ⊗₀ X) ⊗₀ (unit ⊗₀ Y) ⟩
              λ⇒ ⊗₁ λ⇒
            ≈ λ⇒
            ⟩

    unitʳ : [ (X ⊗₀ Y) ⊗₀ unit ⇒ (X ⊗₀ Y) ]⟨
              id ⊗₁ λ⇐   ⇒⟨ (X ⊗₀ Y) ⊗₀ (unit ⊗₀ unit) ⟩
              i⇒         ⇒⟨ (X ⊗₀ unit) ⊗₀ (Y ⊗₀ unit) ⟩
              ρ⇒ ⊗₁ ρ⇒
            ≈ ρ⇒
            ⟩

  -- The interchange is a natural isomorphism.

  naturalIso : ⊗ ∘F (⊗ ⁂ ⊗) ≃ ⊗ ∘F MonoidalProduct.⊗ M M
  naturalIso = niHelper (record
    { η       = λ _ → i⇒
    ; η⁻¹     = λ _ → i⇐
    ; commute = λ _ → natural
    ; iso     = λ _ → swapInner.iso
    })
