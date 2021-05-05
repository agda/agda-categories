{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal.Core using (Monoidal)

-- The "four middle interchange" for monoidal categories.
--
-- Aka the "interchange law" or "exchange law" (though those terms are
-- more comonly used in the more general context of composition in
-- 2-categories).

module Categories.Category.Monoidal.Interchange
  {o ℓ e} {C : Category o ℓ e} where

open import Level using (_⊔_)
open import Data.Product using (_,_)

import Categories.Category.Monoidal.Construction.Product as MonoidalProduct
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Braided.Properties
  using (braiding-coherence; inv-Braided; inv-braiding-coherence)
open import Categories.Category.Monoidal.Properties using (module Kelly's)
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Category.Product using (_⁂_; assocˡ)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (_≃_; niHelper)
open import Categories.Morphism C using (_≅_; module ≅)
open import Categories.Morphism.IsoEquiv C using (module _≃_)
open import Categories.Morphism.Reasoning C

private module C = Category C
open C
open Commutation C

private
  variable
    W W₁ W₂ X X₁ X₂ Y Y₁ Y₂ Z Z₁ Z₂ : Obj
    f g h i : X ⇒ Y

-- An abstract definition of an interchange map with the minimal set
-- of coherence laws required to make the tensor product ⊗ of C a
-- monoidal functor.  (See also Categories.Functor.Monoidal.Tensor.)

record HasInterchange (M : Monoidal C) : Set (o ⊔ ℓ ⊔ e) where
  open Monoidal M
  open MonoidalUtilities.Shorthands M

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

-- Shorthands for composing and inverting isomorphisms.

open ≅ using () renaming (refl to idᵢ; sym to _⁻¹)
private
  infixr 9 _∘ᵢ_
  _∘ᵢ_ = λ {X Y Z} f g → ≅.trans {X} {Y} {Z} g f

-- Braided monoidal categories have an interchange map.

module BraidedInterchange {M : Monoidal C} (B : Braided M) where
  open MonoidalReasoning M
  open MonoidalUtilities M
  open Braided B renaming (associator to α)
  open Shorthands

  -- Shorthands for braiding.

  private
    σ : X ⊗₀ Y ≅ Y ⊗₀ X
    σ = braiding.FX≅GX
    module σ  {X Y} = _≅_ (σ {X} {Y})
    σ⇒ = σ.from
    σ⇐ = σ.to

  -- The "four middle interchange" for braided tensor products.

  swapInner : (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ≅ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z)
  swapInner = α ⁻¹ ∘ᵢ idᵢ ⊗ᵢ (α ∘ᵢ σ ⊗ᵢ idᵢ ∘ᵢ α ⁻¹) ∘ᵢ α

  module swapInner {W X Y Z} = _≅_ (swapInner {W} {X} {Y} {Z})
  private
    i⇒ = swapInner.from
    i⇐ = swapInner.to

  -- The interchange is a natural isomorphism.

  swapInner-natural : i⇒ ∘ (f ⊗₁ g) ⊗₁ (h ⊗₁ i) ≈ (f ⊗₁ h) ⊗₁ (g ⊗₁ i) ∘ i⇒
  swapInner-natural {f = f} {g = g} {h = h} {i = i} = begin
      (α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘ (f ⊗₁ g) ⊗₁ (h ⊗₁ i)
    ≈⟨ pullʳ (pullʳ assoc-commute-from) ⟩
      α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ f ⊗₁ g ⊗₁ (h ⊗₁ i) ∘ α⇒
    ≈⟨ refl⟩∘⟨ extendʳ (parallel id-comm-sym (begin
          (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ g ⊗₁ (h ⊗₁ i)
        ≈⟨ pullʳ (pullʳ assoc-commute-to) ⟩
          α⇒ ∘ σ⇒ ⊗₁ id ∘ (g ⊗₁ h) ⊗₁ i ∘ α⇐
        ≈⟨ refl⟩∘⟨ extendʳ (parallel (braiding.⇒.commute _) id-comm-sym) ⟩
          α⇒ ∘ (h ⊗₁ g) ⊗₁ i ∘ σ⇒ ⊗₁ id ∘ α⇐
        ≈⟨ extendʳ assoc-commute-from ⟩
          h ⊗₁ (g ⊗₁ i) ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐
        ∎)) ⟩
      α⇐ ∘ f ⊗₁ h ⊗₁ (g ⊗₁ i) ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
    ≈⟨ extendʳ assoc-commute-to ⟩
      (f ⊗₁ h) ⊗₁ (g ⊗₁ i) ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
    ∎

  swapInner-naturalIsomorphism : ⊗ ∘F (⊗ ⁂ ⊗) ≃ ⊗ ∘F MonoidalProduct.⊗ M M
  swapInner-naturalIsomorphism = niHelper (record
    { η       = λ _ → i⇒
    ; η⁻¹     = λ _ → i⇐
    ; commute = λ _ → swapInner-natural
    ; iso     = λ _ → swapInner.iso
    })

  -- Another version of the interchange that associates differently.
  --
  -- Why are there two versions and what's the difference? The domain
  -- (X₁ ⊗ X₂) ⊗₀ (Y₁ ⊗ Y₂) and codomain (X₁ ⊗ Y₁) ⊗₀ (X₁ ⊗ Y₂) of the
  -- interchange map are perfectly symmetric/balanced. But in order to
  -- apply the braiding to the middle X₂ and Y₁, we need to
  -- re-associate and that breaks the symmetry. We must first
  -- re-associate the whole expression in one direction and then the
  -- larger subterm in the other. This can be done in two ways,
  -- associate to the right first, then to the left, resulting in X₁ ⊗
  -- ((Y₂ ⊗₀ X₁) ⊗ Y₂), or vice versa, resulting in (X₁ ⊗ (Y₂ ⊗₀ X₁))
  -- ⊗ Y₂. The choice is arbitrary and results in two distinct
  -- interchange maps that behave the same way (as witnessed by
  -- swapInner-coherent below).
  --
  -- Why define both? Because the proofs of some coherence laws become
  -- easier when the core of the expression is associated in one
  -- direction vs. the other. For example swapInner-unitˡ is easier to
  -- prove for the second definition, while swapInner-unitʳ is easier
  -- to prove for the first; swapInner-assoc uses both.

  swapInner′ : (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ≅ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z)
  swapInner′ = α ∘ᵢ (α ⁻¹ ∘ᵢ idᵢ ⊗ᵢ σ ∘ᵢ α) ⊗ᵢ idᵢ ∘ᵢ α ⁻¹

  module swapInner′ {W X Y Z} = _≅_ (swapInner′ {W} {X} {Y} {Z})
  private
    j⇒ = swapInner′.from
    j⇐ = swapInner′.to

  -- Derived coherence laws.

  swapInner-coherent : [ (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ⇒ (X₁ ⊗₀ Y₁) ⊗₀ (X₂ ⊗₀ Y₂) ]⟨
                         i⇒
                       ≈ j⇒
                       ⟩
  swapInner-coherent = begin
      α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
    ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      α⇐ ∘ id ⊗₁ α⇒ ∘ id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      α⇐ ∘ id ⊗₁ α⇒ ∘ id ⊗₁ (σ⇒ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ conjugate-from α (idᵢ ⊗ᵢ α) (⟺ pentagon) ⟩
      α⇐ ∘ id ⊗₁ α⇒ ∘ id ⊗₁ (σ⇒ ⊗₁ id) ∘ (α⇒ ∘ α⇒ ⊗₁ id) ∘ α⇐
    ≈˘⟨ pullʳ (pullʳ (extendʳ (pushˡ assoc-commute-from))) ⟩
      (α⇐ ∘ id ⊗₁ α⇒ ∘ α⇒ ∘ (id ⊗₁ σ⇒) ⊗₁ id) ∘ α⇒ ⊗₁ id ∘ α⇐
    ≈⟨ pushʳ sym-assoc ⟩∘⟨refl ⟩
      ((α⇐ ∘ id ⊗₁ α⇒ ∘ α⇒) ∘ (id ⊗₁ σ⇒) ⊗₁ id) ∘ α⇒ ⊗₁ id ∘ α⇐
    ≈⟨ pushˡ (conjugate-from (α ⊗ᵢ idᵢ) α (assoc ○ pentagon)) ⟩∘⟨refl ⟩
      (α⇒ ∘ α⇐ ⊗₁ id ∘ (id ⊗₁ σ⇒) ⊗₁ id) ∘ α⇒ ⊗₁ id ∘ α⇐
    ≈˘⟨ pushʳ (pushʳ (pushˡ split₁ˡ)) ⟩
      α⇒ ∘ α⇐ ⊗₁ id ∘ (id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐
    ≈˘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
      α⇒ ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐
    ∎

  swapInner-assoc : [ ((X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂)) ⊗₀ (Z₁ ⊗₀ Z₂) ⇒
                      (X₁ ⊗₀ (Y₁ ⊗₀ Z₁)) ⊗₀ (X₂ ⊗₀ (Y₂ ⊗₀ Z₂)) ]⟨
                      i⇒ ⊗₁ id    ⇒⟨ ((X₁ ⊗₀ Y₁) ⊗₀ (X₂ ⊗₀ Y₂)) ⊗₀ (Z₁ ⊗₀ Z₂) ⟩
                      i⇒          ⇒⟨ ((X₁ ⊗₀ Y₁) ⊗₀ Z₁) ⊗₀ ((X₂ ⊗₀ Y₂) ⊗₀ Z₂) ⟩
                      α⇒ ⊗₁ α⇒
                    ≈ α⇒          ⇒⟨ (X₁ ⊗₀ X₂) ⊗₀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⟩
                      id ⊗₁ i⇒    ⇒⟨ (X₁ ⊗₀ X₂) ⊗₀ ((Y₁ ⊗₀ Z₁) ⊗₀ (Y₂ ⊗₀ Z₂)) ⟩
                      i⇒
                    ⟩
  swapInner-assoc = begin
      α⇒ ⊗₁ α⇒ ∘ i⇒ ∘ i⇒ ⊗₁ id
    ≈⟨ (begin
        α⇒ ⊗₁ α⇒
      ≈⟨ serialize₂₁ ⟩
        id ⊗₁ α⇒ ∘ α⇒ ⊗₁ id
      ≈⟨ refl⟩∘⟨ switch-fromtoˡ α (switch-fromtoˡ (idᵢ ⊗ᵢ α) pentagon) ⟩
        id ⊗₁ α⇒ ∘ α⇐ ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ α⇒
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ cancelˡ α.isoʳ ⟩∘⟨refl ⟩
        id ⊗₁ α⇒ ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ α⇐ ∘ α⇐) ∘ α⇒ ∘ α⇒
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ pullʳ inv-pentagon ⟩∘⟨refl ⟩
        id ⊗₁ α⇒ ∘ α⇐ ∘ id ⊗₁ ((α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ α⇐) ∘ α⇒ ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
        id ⊗₁ α⇒ ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐) ∘
        id ⊗₁ (id ⊗₁ α⇐) ∘ α⇒ ∘ α⇒
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
        id ⊗₁ α⇒ ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐) ∘
        α⇒ ∘ (id ⊗₁ id) ⊗₁ α⇐ ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
        id ⊗₁ α⇒ ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ id ⊗₁ α⇐ ∘ α⇒
      ∎) ⟩∘⟨refl ⟩
      (id ⊗₁ α⇒ ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ id ⊗₁ α⇐ ∘ α⇒) ∘
      i⇒ ∘ i⇒ ⊗₁ id
    ≈˘⟨ pullˡ (pushˡ (⊗.identity ⟩⊗⟨refl ⟩∘⟨refl)) ⟩
      ((id ⊗₁ id) ⊗₁ α⇒ ∘ α⇐) ∘
      (id ⊗₁ (α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ id ⊗₁ α⇐ ∘ α⇒) ∘
      (α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘
      i⇒ ⊗₁ id
    ≈⟨ ⟺ assoc-commute-to ⟩∘⟨
       pullʳ (pullʳ (pushʳ (pushˡ (pushʳ (pushˡ split₂ˡ))))) ⟩
      (α⇐ ∘ id ⊗₁ (id ⊗₁ α⇒)) ∘ id ⊗₁ (α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘
      ((id ⊗₁ α⇐ ∘ α⇒) ∘ α⇐ ∘ id ⊗₁ α⇒) ∘
      (id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘
      (α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ⊗₁ id
    ≈⟨ pullʳ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ elimˡ (_≅_.isoˡ (α ⁻¹ ∘ᵢ idᵢ ⊗ᵢ α))) ⟩
      α⇐ ∘ id ⊗₁ (id ⊗₁ α⇒) ∘ id ⊗₁ (α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘
      (id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘
      (α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ⊗₁ id
    ≈⟨ refl⟩∘⟨ merge₂ sym-assoc ⟩∘⟨
         pushʳ ((⟺ ⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩∘⟨ split₁ˡ) ⟩
      α⇐ ∘ id ⊗₁ ((id ⊗₁ α⇒ ∘ α⇒) ∘ α⇐ ⊗₁ id ∘ α⇐) ∘
      (α⇒ ∘ (id ⊗₁ id) ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘
      α⇐ ⊗₁ id ∘ (id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ⊗₁ id
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨
         extendʳ (pushˡ (switch-fromtoʳ (α ⊗ᵢ idᵢ) (assoc ○ pentagon))) ⟩∘⟨
         extendʳ assoc-commute-from ⟩∘⟨refl ⟩
      α⇐ ∘ id ⊗₁ ((α⇒ ∘ α⇒) ∘ (α⇐ ⊗₁ id ∘ α⇐ ⊗₁ id) ∘ α⇐) ∘
      (id ⊗₁ (id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐)) ∘ (α⇒ ∘ α⇒)) ∘ α⇐ ⊗₁ id ∘
      (id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ⊗₁ id
    ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ pushʳ (refl⟩∘⟨ split₁ˡ ⟩∘⟨refl) ⟩∘⟨
         pushʳ (extendʳ (switch-fromtoʳ (α ⊗ᵢ idᵢ) (assoc ○ pentagon))) ⟩
      α⇐ ∘ id ⊗₁ (α⇒ ∘ α⇒ ∘ (α⇐ ∘ α⇐) ⊗₁ id ∘ α⇐) ∘
      id ⊗₁ (id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐)) ∘ id ⊗₁ α⇒ ∘ α⇒ ∘
      (id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ⊗₁ id
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
      α⇐ ∘ id ⊗₁ (α⇒ ∘ α⇒ ∘ (α⇐ ∘ α⇐) ⊗₁ id ∘ α⇐) ∘
      id ⊗₁ (id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐)) ∘ id ⊗₁ α⇒ ∘ α⇒ ∘
      (id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐)) ⊗₁ id ∘ α⇒ ⊗₁ id
    ≈⟨ refl⟩∘⟨ merge₂ assoc²' ○ (refl⟩∘⟨ refl⟩∘⟨ assoc) ⟩∘⟨
         refl⟩∘⟨ extendʳ assoc-commute-from ⟩
      α⇐ ∘ id ⊗₁ (α⇒ ∘ α⇒ ∘ (α⇐ ∘ α⇐) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐)) ∘
      id ⊗₁ α⇒ ∘
      id ⊗₁ ((α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id) ∘ α⇒ ∘ α⇒ ⊗₁ id
    ≈⟨ refl⟩∘⟨ merge₂ (assoc²' ○ (refl⟩∘⟨ refl⟩∘⟨ assoc²')) ⟩∘⟨
         refl⟩∘⟨ switch-fromtoˡ (idᵢ ⊗ᵢ α) pentagon ⟩
      α⇐ ∘ id ⊗₁ (α⇒ ∘ α⇒ ∘ (α⇐ ∘ α⇐) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘
      id ⊗₁ ((α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ α⇒
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      α⇐ ∘ id ⊗₁
        (α⇒ ∘ α⇒ ∘ (α⇐ ∘ α⇐) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘
      id ⊗₁ ((α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ α⇒
    ≈⟨ refl⟩∘⟨ merge₂ assoc²' ○ (refl⟩∘⟨ refl⟩∘⟨ (assoc²' ○
        (refl⟩∘⟨ refl⟩∘⟨ assoc))) ⟩∘⟨ Equiv.refl ⟩
      α⇐ ∘ id ⊗₁ (α⇒ ∘
        α⇒ ∘ (α⇐ ∘ α⇐) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘
        (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ α⇒
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ pushʳ (begin
        α⇒ ∘ (α⇐ ∘ α⇐) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘
        (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (pushˡ split₂ˡ) ⟩
        α⇒ ∘ (α⇐ ∘ α⇐) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id) ∘ (id ⊗₁ α⇐ ∘ α⇒) ∘
        (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (extendʳ assoc-commute-to ○ (refl⟩∘⟨ sym-assoc)) ⟩
        α⇒ ∘ (α⇐ ∘ α⇐) ⊗₁ id ∘ (id ⊗₁ σ⇒) ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ α⇐ ∘ α⇒)) ∘
        (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○
           (conjugate-to α (α ⊗ᵢ idᵢ) (sym-assoc ○ inv-pentagon))) ⟩∘⟨refl ⟩
        α⇒ ∘ (α⇐ ∘ α⇐) ⊗₁ id ∘ (id ⊗₁ σ⇒) ⊗₁ id ∘ (α⇒ ⊗₁ id ∘ α⇐) ∘
        (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐
      ≈˘⟨ refl⟩∘⟨ split₁ Equiv.refl ⟩∘⟨
            pushʳ (refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl) ⟩
        α⇒ ∘ ((α⇐ ∘ α⇐) ∘ id ⊗₁ σ⇒) ⊗₁ id ∘ α⇒ ⊗₁ id ∘ α⇐ ∘
        (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ (id ⊗₁ id) ∘ α⇐
      ≈⟨ refl⟩∘⟨ merge₁ assoc² ⟩∘⟨ extendʳ assoc-commute-to ⟩
        α⇒ ∘ (α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘
        ((α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ α⇐
      ≈˘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
        α⇒ ∘ ((α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ∘ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id) ⊗₁ id ∘
        α⇐ ∘ α⇐
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ inv-pentagon) ⟩
        α⇒ ∘ ((α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ∘ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id) ⊗₁ id ∘
        α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇐
      ≈⟨ refl⟩∘⟨ pullˡ (⟺ split₁ˡ ○ (assoc ⟩⊗⟨refl)) ⟩
        α⇒ ∘
        ((α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ∘ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐) ⊗₁ id ∘
        α⇐ ∘ id ⊗₁ α⇐
      ≈⟨ refl⟩∘⟨ (begin
          (α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ∘ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐
        ≈⟨ pushˡ (pushʳ sym-assoc) ⟩
          (α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐
        ≈⟨ (refl⟩∘⟨ extendʳ (pushʳ split₁ˡ)) ⟩
          (α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒) ∘ (α⇒ ∘ α⇒ ⊗₁ id) ∘ (σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐
        ≈⟨ pushʳ (switch-fromtoˡ (idᵢ ⊗ᵢ α) pentagon ⟩∘⟨ pushˡ split₁ˡ) ⟩
          ((α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒) ∘ (id ⊗₁ α⇐ ∘ α⇒ ∘ α⇒)) ∘
          (σ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐ ⊗₁ id ∘ α⇐
        ≈⟨ pushˡ (sym-assoc ○ (pullˡ (pullʳ assoc ⟩∘⟨refl))) ⟩
          ((α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ id ⊗₁ α⇐) ∘ α⇒) ∘
          α⇒ ∘ (σ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐ ⊗₁ id ∘ α⇐
        ≈⟨ pullʳ (refl⟩∘⟨ extendʳ assoc-commute-from) ⟩
          (α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ id ⊗₁ α⇐) ∘ α⇒ ∘
          σ⇒ ⊗₁ (id ⊗₁ id) ∘ α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐
        ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ ⟺ split₂ˡ) ⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity ⟩∘⟨
             conjugate-from (idᵢ ⊗ᵢ (α ⁻¹)) (α ⁻¹) inv-pentagon) ⟩
          (α⇐ ∘ α⇐ ∘ id ⊗₁ (σ⇒ ∘ α⇐)) ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒
        ≈˘⟨ extendʳ (sym-assoc ○ inv-pentagon) ⟩∘⟨refl ⟩
          (α⇐ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ α⇐) ∘ id ⊗₁ (σ⇒ ∘ α⇐)) ∘
          α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒
        ≈˘⟨ (refl⟩∘⟨ pushʳ split₂ˡ) ⟩∘⟨refl ⟩
          (α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (α⇐ ∘ σ⇒ ∘ α⇐)) ∘
          α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒
        ≈˘⟨ pushˡ ((refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨
              (sym-assoc ○ hexagon₂ ○ assoc)) ⟩∘⟨refl) ⟩
          ((α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ σ⇒)) ∘ α⇒) ∘
          σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒
        ≈⟨ pushˡ (pushʳ (pushʳ split₂ˡ)) ⟩∘⟨refl ⟩
          ((α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ σ⇒ ⊗₁ id) ∘ id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒) ∘
          σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒
        ≈⟨ pushʳ (pushˡ split₂ˡ) ⟩∘⟨refl ⟩
          (((α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ σ⇒ ⊗₁ id) ∘ id ⊗₁ α⇐) ∘
            id ⊗₁ id ⊗₁ σ⇒ ∘ α⇒) ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒
        ≈⟨ ((pushˡ (pushʳ assoc-commute-to) ⟩∘⟨
             ⟺ assoc-commute-from) ○ (pullʳ sym-assoc)) ⟩∘⟨refl ⟩
          ((α⇐ ⊗₁ id ∘ (id ⊗₁ σ⇒) ⊗₁ id) ∘ ((α⇐ ∘ id ⊗₁ α⇐) ∘ α⇒) ∘
            (id ⊗₁ id) ⊗₁ σ⇒) ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒
        ≈⟨ pullˡ (⟺ split₁ˡ ⟩∘⟨
             conjugate-from α (idᵢ ⊗ᵢ α ∘ᵢ α) (⟺ (assoc ○ pentagon)))
             ⟩∘⟨refl ⟩
          (((α⇐ ∘ id ⊗₁ σ⇒) ⊗₁ id ∘ α⇒ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ id) ⊗₁ σ⇒) ∘
          σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒
        ≈⟨ (pullˡ (⟺ split₁ˡ) ⟩∘⟨ ⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
          ((((α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒) ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘
          σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒
        ≈⟨ extend² (⟺ serialize₂₁ ○ serialize₁₂) ⟩
          ((((α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒) ⊗₁ id ∘ α⇐) ∘ σ⇒ ⊗₁ id) ∘
          id ⊗₁ σ⇒ ∘ α⇐ ∘ id ⊗₁ α⇒
        ≈˘⟨ pushʳ (refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity) ⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
          (((α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒) ⊗₁ id ∘ α⇐ ∘ σ⇒ ⊗₁ id ⊗₁ id) ∘
          (id ⊗₁ id) ⊗₁ σ⇒ ∘ α⇐ ∘ id ⊗₁ α⇒
        ≈⟨ pushʳ assoc-commute-to ⟩∘⟨ extendʳ (⟺ assoc-commute-to) ⟩
          ((((α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒) ⊗₁ id ∘ (σ⇒ ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘
          α⇐ ∘ id ⊗₁ id ⊗₁ σ⇒ ∘ id ⊗₁ α⇒
        ≈˘⟨ ((sym-assoc ○ sym-assoc) ⟩⊗⟨refl ○ split₁ˡ) ⟩∘⟨refl ⟩∘⟨
            refl⟩∘⟨ split₂ˡ ⟩
          (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘
          α⇐ ∘ id ⊗₁ (id ⊗₁ σ⇒ ∘ α⇒)
        ≈˘⟨ extend² (sym-assoc ○ inv-pentagon) ⟩
          (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ⊗₁ id) ∘ α⇐ ⊗₁ id) ∘
          (α⇐ ∘ id ⊗₁ α⇐) ∘ id ⊗₁ (id ⊗₁ σ⇒ ∘ α⇒)
        ≈˘⟨ split₁ˡ ⟩∘⟨ pushʳ split₂ˡ ⟩
          ((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id ∘
          α⇐ ∘ id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒)
        ∎) ⟩⊗⟨refl ⟩∘⟨refl ⟩
        α⇒ ∘ (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id ∘ α⇐ ∘
          id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒)) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇐
      ≈⟨ (refl⟩∘⟨ pushˡ ((sym-assoc ⟩⊗⟨refl) ○ split₁ˡ)) ⟩
        α⇒ ∘ (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id ∘ α⇐) ⊗₁ id ∘
        (id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒)) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇐
      ≈⟨ (refl⟩∘⟨ split₁ˡ ⟩∘⟨ extendʳ (⟺ assoc-commute-to)) ○ pushʳ assoc ⟩
        (α⇒ ∘ (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id) ⊗₁ id) ∘
        α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ id ⊗₁ α⇐
      ≈⟨ pushˡ assoc-commute-from ⟩
        ((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ (id ⊗₁ id) ∘ α⇒ ∘
        α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ id ⊗₁ α⇐
      ≈˘⟨ refl⟩∘⟨ pullʳ (pullʳ (refl⟩∘⟨ split₂ˡ)) ⟩
        ((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ (id ⊗₁ id) ∘
        (α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ ((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐)
      ≈˘⟨ pullʳ (pullˡ (conjugate-from (α ∘ᵢ α ⊗ᵢ idᵢ) α pentagon)) ⟩
        (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ (id ⊗₁ id) ∘ α⇐) ∘
        id ⊗₁ α⇒ ∘ id ⊗₁ ((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐)
      ≈⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟩∘⟨ ⟺ split₂ˡ ⟩
        (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id ∘ α⇐) ∘
        id ⊗₁ (α⇒ ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐)
      ≡⟨⟩
        (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id ∘ α⇐) ∘ id ⊗₁ j⇒
      ≈˘⟨ switch-fromtoʳ α (switch-fromtoˡ α (⟺ hexagon₁))
            ⟩⊗⟨refl ⟩∘⟨refl ⟩∘⟨refl ⟩
        (σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ j⇒
      ∎) ⟩∘⟨refl ⟩
      α⇐ ∘ id ⊗₁ ((α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ j⇒) ∘ α⇒ ∘ α⇒
    ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ id ⊗₁ j⇒ ∘ α⇒ ∘ α⇒
    ≈˘⟨ pullʳ (pullʳ (extendʳ assoc-commute-from)) ⟩
      (α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘ (id ⊗₁ id) ⊗₁ j⇒ ∘ α⇒
    ≡⟨⟩
      i⇒ ∘ (id ⊗₁ id) ⊗₁ j⇒ ∘ α⇒
    ≈⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨ ⟺ swapInner-coherent ⟩∘⟨refl ⟩
      i⇒ ∘ id ⊗₁ i⇒ ∘ α⇒
    ∎
    where inv-pentagon = λ {W X Y Z} → _≃_.to-≈ (pentagon-iso {W} {X} {Y} {Z})

  swapInner-unitˡ : [ unit ⊗₀ (X ⊗₀ Y) ⇒ (X ⊗₀ Y) ]⟨
                      λ⇐ ⊗₁ id         ⇒⟨ (unit ⊗₀ unit) ⊗₀ (X ⊗₀ Y) ⟩
                      i⇒               ⇒⟨ (unit ⊗₀ X) ⊗₀ (unit ⊗₀ Y) ⟩
                      λ⇒ ⊗₁ λ⇒
                    ≈ λ⇒
                    ⟩
  swapInner-unitˡ = begin
      λ⇒ ⊗₁ λ⇒ ∘ i⇒ ∘ λ⇐ ⊗₁ id
    ≈⟨ refl⟩∘⟨ swapInner-coherent ⟩∘⟨ (Kelly₃′ ⟩⊗⟨refl) ⟩
      λ⇒ ⊗₁ λ⇒ ∘ j⇒ ∘ ρ⇐ ⊗₁ id
    ≡⟨⟩
      λ⇒ ⊗₁ λ⇒ ∘ (α⇒ ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐) ∘ ρ⇐ ⊗₁ id
    ≈⟨ pullˡ (pushˡ serialize₁₂) ⟩
      (λ⇒ ⊗₁ id ∘ id ⊗₁ λ⇒ ∘ α⇒ ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐) ∘ ρ⇐ ⊗₁ id
    ≈⟨ (refl⟩∘⟨ (begin
        id ⊗₁ λ⇒ ∘ α⇒ ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐
      ≈⟨ pullˡ triangle ⟩
        ρ⇒ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐
      ≈˘⟨ pushˡ split₁ˡ ⟩
        (ρ⇒ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐
      ≈⟨ (pullˡ Kelly₂′ ⟩⊗⟨refl ⟩∘⟨refl) ⟩
        (id ⊗₁ ρ⇒ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐
      ≈˘⟨ pushˡ split₂ˡ ⟩⊗⟨refl ⟩∘⟨refl ⟩
        (id ⊗₁ (ρ⇒ ∘ σ⇒) ∘ α⇒) ⊗₁ id ∘ α⇐
      ≈⟨ (refl⟩⊗⟨ σ⁻¹-coherence ⟩∘⟨refl) ⟩⊗⟨refl ⟩∘⟨refl ⟩
        (id ⊗₁ λ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐
      ≈⟨ triangle ⟩⊗⟨refl ⟩∘⟨refl ⟩
        (ρ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐
      ≈˘⟨ assoc-commute-to ⟩
        α⇐ ∘ ρ⇒ ⊗₁ (id ⊗₁ id)
      ∎)) ⟩∘⟨refl ⟩
      (λ⇒ ⊗₁ id ∘ α⇐ ∘ ρ⇒ ⊗₁ (id ⊗₁ id)) ∘ ρ⇐ ⊗₁ id
    ≈⟨ (sym-assoc ○ (Kelly₁′ ⟩∘⟨ refl⟩⊗⟨ ⊗.identity)) ⟩∘⟨refl ⟩
      (λ⇒ ∘ ρ⇒ ⊗₁ id) ∘ ρ⇐ ⊗₁ id
    ≈⟨ cancelʳ (_≅_.isoʳ (unitorʳ ⊗ᵢ idᵢ)) ⟩
      λ⇒
    ∎
    where
      Kelly₁′       = ⟺ (switch-fromtoʳ α (Kelly's.coherence₁ M))
      Kelly₂′       = ⟺ (switch-fromtoʳ α (Kelly's.coherence₂ M))
      Kelly₃′       = _≃_.to-≈ (Kelly's.coherence-iso₃ M)
      σ⁻¹-coherence = inv-braiding-coherence (inv-Braided B)

  swapInner-unitʳ : [ (X ⊗₀ Y) ⊗₀ unit ⇒ (X ⊗₀ Y) ]⟨
                      id ⊗₁ λ⇐         ⇒⟨ (X ⊗₀ Y) ⊗₀ (unit ⊗₀ unit) ⟩
                      i⇒               ⇒⟨ (X ⊗₀ unit) ⊗₀ (Y ⊗₀ unit) ⟩
                      ρ⇒ ⊗₁ ρ⇒
                    ≈ ρ⇒
                    ⟩
  swapInner-unitʳ = begin
      ρ⇒ ⊗₁ ρ⇒ ∘ i⇒ ∘ id ⊗₁ λ⇐
    ≡⟨⟩
      ρ⇒ ⊗₁ ρ⇒ ∘ (α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘ id ⊗₁ λ⇐
    ≈⟨ pullˡ (pushˡ serialize₂₁) ⟩
      (id ⊗₁ ρ⇒ ∘ ρ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘ id ⊗₁ λ⇐
    ≈⟨ (refl⟩∘⟨ (begin
        ρ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
      ≈˘⟨ pushˡ (switch-fromtoʳ α triangle) ⟩
        id ⊗₁ λ⇒ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
      ≈˘⟨ pushˡ split₂ˡ ⟩
        id ⊗₁ (λ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
      ≈⟨ refl⟩⊗⟨ pullˡ (Kelly's.coherence₁ M) ⟩∘⟨refl ⟩
        id ⊗₁ (λ⇒ ⊗₁ id ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
      ≈˘⟨ refl⟩⊗⟨ pushˡ split₁ˡ ⟩∘⟨refl ⟩
        id ⊗₁ ((λ⇒ ∘ σ⇒) ⊗₁ id ∘ α⇐) ∘ α⇒
      ≈⟨ refl⟩⊗⟨ (braiding-coherence B ⟩⊗⟨refl ⟩∘⟨refl) ⟩∘⟨refl ⟩
        id ⊗₁ (ρ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
      ≈˘⟨ refl⟩⊗⟨ switch-fromtoʳ α triangle ⟩∘⟨refl ⟩
        id ⊗₁ (id ⊗₁ λ⇒) ∘ α⇒
      ≈˘⟨ assoc-commute-from ⟩
        α⇒ ∘ (id ⊗₁ id) ⊗₁ λ⇒
      ∎)) ⟩∘⟨refl ⟩
      (id ⊗₁ ρ⇒ ∘ α⇒ ∘ (id ⊗₁ id) ⊗₁ λ⇒) ∘ id ⊗₁ λ⇐
    ≈⟨ (sym-assoc ○ (Kelly's.coherence₂ M ⟩∘⟨ ⊗.identity ⟩⊗⟨refl)) ⟩∘⟨refl ⟩
      (ρ⇒ ∘ id ⊗₁ λ⇒) ∘ id ⊗₁ λ⇐
    ≈⟨ cancelʳ (_≅_.isoʳ (idᵢ ⊗ᵢ unitorˡ)) ⟩
      ρ⇒
    ∎

  swapInner-braiding : [ (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ⇒ (Y ⊗₀ Z) ⊗₀ (W ⊗₀ X) ]⟨
                         i⇒         ⇒⟨ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z) ⟩
                         σ⇒ ⊗₁ σ⇒   ⇒⟨ (Y ⊗₀ W) ⊗₀ (Z ⊗₀ X) ⟩
                         i⇒
                       ≈ σ⇒
                       ⟩
  swapInner-braiding = begin
      i⇒ ∘ σ⇒ ⊗₁ σ⇒ ∘ i⇒
    ≡⟨⟩
      i⇒ ∘ σ⇒ ⊗₁ σ⇒ ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
    ≈⟨ swapInner-coherent ⟩∘⟨ pushˡ serialize₁₂ ⟩
      j⇒ ∘ σ⇒ ⊗₁ id ∘ id ⊗₁ σ⇒ ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
    ≈˘⟨ ((refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity) ⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl) ○ assoc ⟩
      ((α⇒ ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐) ∘ σ⇒ ⊗₁ (id ⊗₁ id)) ∘
      (id ⊗₁ id) ⊗₁ σ⇒ ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
    ≈⟨ pullʳ (pullʳ assoc-commute-to) ⟩∘⟨ extendʳ (⟺ assoc-commute-to) ⟩
      (α⇒ ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ (σ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐) ∘
      α⇐ ∘ id ⊗₁ (id ⊗₁ σ⇒) ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
    ≈˘⟨ (refl⟩∘⟨ pushˡ split₁ˡ) ⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      (α⇒ ∘ ((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ∘ σ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐) ∘
      α⇐ ∘ id ⊗₁ (id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
    ≈⟨ (refl⟩∘⟨ pullʳ (assoc ○ hexagon₁) ⟩⊗⟨refl ⟩∘⟨refl) ⟩∘⟨
        refl⟩∘⟨ refl⟩⊗⟨ (⟺ assoc ○ (pullˡ (assoc ○ hexagon₁))) ⟩∘⟨refl ⟩
      (α⇒ ∘ (α⇐ ∘ α⇒ ∘ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐) ∘
      α⇐ ∘ id ⊗₁ ((α⇒ ∘ σ⇒ ∘ α⇒) ∘ α⇐) ∘ α⇒
    ≈⟨ (refl⟩∘⟨ cancelˡ α.isoˡ ⟩⊗⟨refl ⟩∘⟨refl) ⟩∘⟨
        refl⟩∘⟨ refl⟩⊗⟨ pullʳ (cancelʳ α.isoʳ) ⟩∘⟨refl ⟩
      (α⇒ ∘ (σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐) ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒) ∘ α⇒
    ≈⟨ extendʳ (pushʳ split₁ˡ) ⟩∘⟨ extendʳ (pushʳ split₂ˡ) ⟩
      ((α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇒ ⊗₁ id ∘ α⇐) ∘ (α⇐ ∘ id ⊗₁ α⇒) ∘ id ⊗₁ σ⇒ ∘ α⇒
    ≈˘⟨ extendʳ (pushʳ (pushʳ assoc)) ⟩
      (α⇒ ∘ σ⇒ ⊗₁ id) ∘ (α⇒ ⊗₁ id ∘ (α⇐ ∘ α⇐) ∘ id ⊗₁ α⇒) ∘ id ⊗₁ σ⇒ ∘ α⇒
    ≈˘⟨ refl⟩∘⟨ switch-tofromˡ (α ⊗ᵢ idᵢ)
                  (switch-tofromʳ (idᵢ ⊗ᵢ α) inv-pentagon) ⟩∘⟨refl ⟩
      (α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒
    ≈⟨ pullʳ (sym-assoc ○ pullˡ hexagon₂) ⟩
      α⇒ ∘ ((α⇐ ∘ σ⇒) ∘ α⇐) ∘ α⇒
    ≈⟨ (refl⟩∘⟨ cancelʳ α.isoˡ) ⟩
      α⇒ ∘ (α⇐ ∘ σ⇒)
    ≈⟨ cancelˡ α.isoʳ ⟩
      σ⇒
    ∎
    where inv-pentagon = _≃_.to-≈ pentagon-iso

  -- Braided monoidal categories have an interchange.

  hasInterchange : HasInterchange M
  hasInterchange = record
    { swapInner  = swapInner
    ; natural    = swapInner-natural
    ; assoc      = swapInner-assoc
    ; unitˡ      = swapInner-unitˡ
    ; unitʳ      = swapInner-unitʳ
    }
  open HasInterchange hasInterchange public using (naturalIso)

-- Extra identities that hold only for symmetric monoidal categories.

module SymmetricInterchange {M : Monoidal C} (S : Symmetric M) where
  open MonoidalReasoning M
  open MonoidalUtilities M
  open Symmetric S renaming (associator to α)
  open Shorthands
  open BraidedInterchange braided public
  private
    i⇒ = swapInner.from
    i⇐ = swapInner.to
    σ⇒ = λ {X Y} → braiding.⇒.η (X , Y)
    σ⇐ = λ {X Y} → braiding.⇐.η (X , Y)

  swapInner-commutative : [ (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ⇒
                            (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ]⟨
                             i⇒    ⇒⟨ (X₁ ⊗₀ Y₁) ⊗₀ (X₂ ⊗₀ Y₂) ⟩
                             i⇒
                           ≈ id
                           ⟩
  swapInner-commutative = begin
      i⇒ ∘ i⇒
    ≈⟨ pullʳ (cancelInner α.isoʳ) ⟩
      α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
    ≈˘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      α⇐ ∘ id ⊗₁ ((α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (∘-resp-≈ʳ sym-assoc ○ α[σ⊗1]α⁻¹.isoʳ) ⟩∘⟨refl ⟩
      α⇐ ∘ id ⊗₁ id ∘ α⇒
    ≈⟨ refl⟩∘⟨ ⊗.identity ⟩∘⟨refl ⟩
      α⇐ ∘ id ∘ α⇒
    ≈⟨ ∘-resp-≈ʳ identityˡ ○ α.isoˡ ⟩
      id
    ∎
    where module α[σ⊗1]α⁻¹ = _≅_ (α ∘ᵢ braided-iso ⊗ᵢ idᵢ ∘ᵢ α ⁻¹)

  swapInner-iso : (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ≅ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z)
  swapInner-iso = record
    { from = i⇒
    ; to   = i⇒
    ; iso  = record
      { isoˡ = swapInner-commutative
      ; isoʳ = swapInner-commutative
      }
    }

  swapInner-braiding′ : [ (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ⇒ (Y ⊗₀ W) ⊗₀ (Z ⊗₀ X) ]⟨
                          i⇒         ⇒⟨ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z) ⟩
                          σ⇒ ⊗₁ σ⇒
                        ≈ σ⇒         ⇒⟨ (Y ⊗₀ Z) ⊗₀ (W ⊗₀ X) ⟩
                          i⇒
                        ⟩
  swapInner-braiding′ = switch-fromtoˡ swapInner-iso swapInner-braiding
