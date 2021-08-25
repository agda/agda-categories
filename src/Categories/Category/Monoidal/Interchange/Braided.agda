{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)

-- Braided monoidal categories satisfy the "four middle interchange"

module Categories.Category.Monoidal.Interchange.Braided
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (B : Braided M) where

open import Level using (_⊔_)
open import Data.Product using (_,_)

import Categories.Category.Construction.Core C as Core
import Categories.Category.Monoidal.Construction.Product as MonoidalProduct
open import Categories.Category.Monoidal.Braided.Properties as BraidedProps
  using (braiding-coherence; inv-Braided; inv-braiding-coherence)
open import Categories.Category.Monoidal.Interchange using (HasInterchange)
open import Categories.Category.Monoidal.Properties using (module Kelly's)
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Category.Product using (_⁂_; assocˡ)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (_≃_; niHelper)
open import Categories.Morphism.Reasoning C

open Category C
open Commutation C

private
  variable
    W W₁ W₂ X X₁ X₂ Y Y₁ Y₂ Z Z₁ Z₂ : Obj
    f g h i : X ⇒ Y

-- Braided monoidal categories have an interchange map.

open MonoidalReasoning M
open MonoidalUtilities M
open Braided B renaming (associator to α)
open Core.Shorthands            -- for idᵢ, _∘ᵢ_, ...
open Shorthands                 -- for λ⇒, ρ⇒, α⇒, ...
open BraidedProps.Shorthands B  -- for σ⇒, ...

-- The "four middle interchange" for braided tensor products.

swapInner : (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ≅ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z)
swapInner = α ⁻¹ ∘ᵢ idᵢ ⊗ᵢ (α ∘ᵢ σ ⊗ᵢ idᵢ ∘ᵢ α ⁻¹) ∘ᵢ α

module swapInner {W X Y Z} = _≅_ (swapInner {W} {X} {Y} {Z})
private
  i⇒ = swapInner.from
  i⇐ = swapInner.to

-- to shorten things, it is convenient to name some items that recur
-- swapˡ is the inner part of 'swapInner'
private
  swapˡ : X ⊗₀ (Y ⊗₀ Z) ⇒ Y ⊗₀ (X ⊗₀ Z)
  swapˡ = α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐

  swapˡ-act :  swapˡ ∘ g ⊗₁ (h ⊗₁ i) ≈ h ⊗₁ (g ⊗₁ i) ∘ swapˡ
  swapˡ-act {g = g} {h = h} {i = i} = begin
    (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ g ⊗₁ (h ⊗₁ i)    ≈⟨ pullʳ (pullʳ assoc-commute-to) ⟩
    α⇒ ∘ σ⇒ ⊗₁ id ∘ (g ⊗₁ h) ⊗₁ i ∘ α⇐      ≈⟨ refl⟩∘⟨ extendʳ (parallel (braiding.⇒.commute _) id-comm-sym) ⟩
    α⇒ ∘ (h ⊗₁ g) ⊗₁ i ∘ σ⇒ ⊗₁ id ∘ α⇐      ≈⟨ extendʳ assoc-commute-from ⟩
    h ⊗₁ (g ⊗₁ i) ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐      ∎

swapInner-natural : i⇒ ∘ (f ⊗₁ g) ⊗₁ (h ⊗₁ i) ≈ (f ⊗₁ h) ⊗₁ (g ⊗₁ i) ∘ i⇒
swapInner-natural {f = f} {g = g} {h = h} {i = i} = begin
    (α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒) ∘ (f ⊗₁ g) ⊗₁ (h ⊗₁ i)  ≈⟨ pullʳ (pullʳ assoc-commute-from) ⟩
    α⇐ ∘ id ⊗₁ swapˡ ∘ f ⊗₁ g ⊗₁ (h ⊗₁ i) ∘ α⇒      ≈⟨ refl⟩∘⟨ extendʳ (parallel id-comm-sym swapˡ-act) ⟩
    α⇐ ∘ f ⊗₁ h ⊗₁ (g ⊗₁ i) ∘ id ⊗₁ swapˡ ∘ α⇒      ≈⟨ extendʳ assoc-commute-to ⟩
    (f ⊗₁ h) ⊗₁ (g ⊗₁ i) ∘ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒    ∎

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

  swapʳ : (X ⊗₀ Y) ⊗₀ Z ⇒ (X ⊗₀ Z) ⊗₀ Y
  swapʳ = α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒

-- Derived coherence laws.

swapInner-coherent : [ (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ⇒ (X₁ ⊗₀ Y₁) ⊗₀ (X₂ ⊗₀ Y₂) ]⟨
                       i⇒
                     ≈ j⇒
                     ⟩
swapInner-coherent = begin
    α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒                       ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    α⇐ ∘ id ⊗₁ α⇒ ∘ id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    α⇐ ∘ id ⊗₁ α⇒ ∘ id ⊗₁ (σ⇒ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ conjugate-from α (idᵢ ⊗ᵢ α) (⟺ pentagon) ⟩
    α⇐ ∘ id ⊗₁ α⇒ ∘ id ⊗₁ (σ⇒ ⊗₁ id) ∘ (α⇒ ∘ α⇒ ⊗₁ id) ∘ α⇐   ≈˘⟨ pullʳ (pullʳ (extendʳ (pushˡ assoc-commute-from))) ⟩
    (α⇐ ∘ id ⊗₁ α⇒ ∘ α⇒ ∘ (id ⊗₁ σ⇒) ⊗₁ id) ∘ α⇒ ⊗₁ id ∘ α⇐   ≈⟨ pushʳ sym-assoc ⟩∘⟨refl ⟩
    ((α⇐ ∘ id ⊗₁ α⇒ ∘ α⇒) ∘ (id ⊗₁ σ⇒) ⊗₁ id) ∘ α⇒ ⊗₁ id ∘ α⇐ ≈⟨ pushˡ (conjugate-from (α ⊗ᵢ idᵢ) α (assoc ○ pentagon)) ⟩∘⟨refl ⟩
    (α⇒ ∘ α⇐ ⊗₁ id ∘ (id ⊗₁ σ⇒) ⊗₁ id) ∘ α⇒ ⊗₁ id ∘ α⇐         ≈˘⟨ pushʳ (pushʳ (pushˡ split₁ˡ)) ⟩
    α⇒ ∘ α⇐ ⊗₁ id ∘ (id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐                 ≈˘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
    α⇒ ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐                       ∎

private
  α-mid : ∀ {X} {Y} {Z} {W} → X ⊗₀ ((Y ⊗₀ Z) ⊗₀ W) ⇒ (X ⊗₀ Y) ⊗₀ (Z ⊗₀ W)
  α-mid = α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐

private
  serialize-assoc : α⇒ {X₁} {Y₁} {Z₁} ⊗₁ α⇒ {X₂} {Y₂} {Z₂} ≈ id ⊗₁ α⇒ ∘ α⇐ ∘ id ⊗₁ (α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ id ⊗₁ α⇐ ∘ α⇒
  serialize-assoc = begin
    α⇒ ⊗₁ α⇒                                           ≈⟨ serialize₂₁ ⟩
    id ⊗₁ α⇒ ∘ α⇒ ⊗₁ id                                ≈⟨ refl⟩∘⟨ (begin
      α⇒ ⊗₁ id                                             ≈⟨ switch-fromtoˡ α (switch-fromtoˡ (idᵢ ⊗ᵢ α) pentagon) ⟩
      α⇐ ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ α⇒                             ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ cancelˡ α.isoʳ ⟩∘⟨refl ⟩
      α⇐ ∘ id ⊗₁ (α⇒ ∘ α⇐ ∘ α⇐) ∘ α⇒ ∘ α⇒                 ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ pullʳ pentagon-inv ⟩∘⟨refl ⟩
      α⇐ ∘ id ⊗₁ (α-mid ∘ id ⊗₁ α⇐) ∘ α⇒ ∘ α⇒             ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      α⇐ ∘ id ⊗₁ α-mid ∘ id ⊗₁ (id ⊗₁ α⇐) ∘ α⇒ ∘ α⇒       ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
      α⇐ ∘ id ⊗₁ α-mid ∘ α⇒ ∘ (id ⊗₁ id) ⊗₁ α⇐ ∘ α⇒       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
      α⇐ ∘ id ⊗₁ α-mid ∘ α⇒ ∘ id ⊗₁ α⇐ ∘ α⇒               ∎) ⟩
    id ⊗₁ α⇒ ∘ α⇐ ∘ id ⊗₁ α-mid ∘ α⇒ ∘ id ⊗₁ α⇐ ∘ α⇒  ∎

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
    α⇒ ⊗₁ α⇒ ∘ i⇒ ∘ i⇒ ⊗₁ id                                   ≈⟨ serialize-assoc ⟩∘⟨refl ⟩
    (id ⊗₁ α⇒ ∘ α⇐ ∘ id ⊗₁ α-mid ∘ α⇒ ∘ id ⊗₁ α⇐ ∘ α⇒) ∘ i⇒ ∘ i⇒ ⊗₁ id  ≈˘⟨ pullˡ (pushˡ (⊗.identity ⟩⊗⟨refl ⟩∘⟨refl)) ⟩
    ((id ⊗₁ id) ⊗₁ α⇒ ∘ α⇐) ∘ (id ⊗₁ α-mid ∘ α⇒ ∘ id ⊗₁ α⇐ ∘ α⇒) ∘ i⇒ ∘ i⇒ ⊗₁ id
                                                                  ≈⟨ ⟺ assoc-commute-to ⟩∘⟨ pullʳ (pullʳ (pushʳ (pushˡ (pushʳ (pushˡ split₂ˡ))))) ⟩
    (α⇐ ∘ id ⊗₁ (id ⊗₁ α⇒)) ∘ id ⊗₁ α-mid ∘ α⇒ ∘
    ((id ⊗₁ α⇐ ∘ α⇒) ∘ α⇐ ∘ id ⊗₁ α⇒) ∘
    (id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘ i⇒ ⊗₁ id
                                                                  ≈⟨ pullʳ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ elimˡ (_≅_.isoˡ (α ⁻¹ ∘ᵢ idᵢ ⊗ᵢ α))) ⟩
    α⇐ ∘ id ⊗₁ (id ⊗₁ α⇒) ∘ id ⊗₁ α-mid ∘ α⇒ ∘
    (id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒) ∘
    i⇒ ⊗₁ id
                                                                  ≈⟨ refl⟩∘⟨ merge₂ sym-assoc ⟩∘⟨ pushʳ ((⟺ ⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩∘⟨ split₁ˡ) ⟩
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
                                                                         (conjugate-to α (α ⊗ᵢ idᵢ) (sym-assoc ○ pentagon-inv))) ⟩∘⟨refl ⟩
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
                                                                  ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ pentagon-inv) ⟩
      α⇒ ∘ ((α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ∘ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id) ⊗₁ id ∘
      α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇐
                                                                  ≈⟨ refl⟩∘⟨ pullˡ (⟺ split₁ˡ ○ (assoc ⟩⊗⟨refl)) ⟩
      α⇒ ∘
      ((α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ∘ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐) ⊗₁ id ∘
      α⇐ ∘ id ⊗₁ α⇐
                                                                  ≈⟨ refl⟩∘⟨ (begin
        (α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ∘ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐            ≈⟨ pushˡ (pushʳ sym-assoc) ⟩
        (α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐            ≈⟨ (refl⟩∘⟨ extendʳ (pushʳ split₁ˡ)) ⟩
        (α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒) ∘ (α⇒ ∘ α⇒ ⊗₁ id) ∘ (σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id ∘ α⇐    ≈⟨ pushʳ (switch-fromtoˡ (idᵢ ⊗ᵢ α) pentagon ⟩∘⟨ pushˡ split₁ˡ) ⟩
        ((α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒) ∘ (id ⊗₁ α⇐ ∘ α⇒ ∘ α⇒)) ∘
        (σ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐ ⊗₁ id ∘ α⇐                                         ≈⟨ pushˡ (sym-assoc ○ (pullˡ (pullʳ assoc ⟩∘⟨refl))) ⟩
        ((α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ id ⊗₁ α⇐) ∘ α⇒) ∘
        α⇒ ∘ (σ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐ ⊗₁ id ∘ α⇐                                   ≈⟨ pullʳ (refl⟩∘⟨ extendʳ assoc-commute-from) ⟩
        (α⇐ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ id ⊗₁ α⇐) ∘ α⇒ ∘
        σ⇒ ⊗₁ (id ⊗₁ id) ∘ α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐                                   ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ ⟺ split₂ˡ) ⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity ⟩∘⟨
           conjugate-from (idᵢ ⊗ᵢ (α ⁻¹)) (α ⁻¹) pentagon-inv) ⟩
        (α⇐ ∘ α⇐ ∘ id ⊗₁ (σ⇒ ∘ α⇐)) ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒            ≈˘⟨ extendʳ (sym-assoc ○ pentagon-inv) ⟩∘⟨refl ⟩
        (α⇐ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ α⇐) ∘ id ⊗₁ (σ⇒ ∘ α⇐)) ∘
        α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒                                           ≈˘⟨ (refl⟩∘⟨ pushʳ split₂ˡ) ⟩∘⟨refl ⟩
        (α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (α⇐ ∘ σ⇒ ∘ α⇐)) ∘
        α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒                                           ≈˘⟨ pushˡ ((refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ (sym-assoc ○ hexagon₂ ○ assoc)) ⟩∘⟨refl) ⟩
        ((α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ σ⇒)) ∘ α⇒) ∘
        σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒                                                ≈⟨ pushˡ (pushʳ (pushʳ split₂ˡ)) ⟩∘⟨refl ⟩
        ((α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ σ⇒ ⊗₁ id) ∘ id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒) ∘
        σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒                                                ≈⟨ pushʳ (pushˡ split₂ˡ) ⟩∘⟨refl ⟩
        (((α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ σ⇒ ⊗₁ id) ∘ id ⊗₁ α⇐) ∘
          id ⊗₁ id ⊗₁ σ⇒ ∘ α⇒) ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒                      ≈⟨ ((pushˡ (pushʳ assoc-commute-to) ⟩∘⟨
                                                                                       ⟺ assoc-commute-from) ○ (pullʳ sym-assoc)) ⟩∘⟨refl ⟩
        ((α⇐ ⊗₁ id ∘ (id ⊗₁ σ⇒) ⊗₁ id) ∘ ((α⇐ ∘ id ⊗₁ α⇐) ∘ α⇒) ∘
          (id ⊗₁ id) ⊗₁ σ⇒) ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒                         ≈⟨ pullˡ (⟺ split₁ˡ ⟩∘⟨
                                                                                           conjugate-from α (idᵢ ⊗ᵢ α ∘ᵢ α) (⟺ (assoc ○ pentagon)))
                                                                                           ⟩∘⟨refl ⟩
        (((α⇐ ∘ id ⊗₁ σ⇒) ⊗₁ id ∘ α⇒ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ id) ⊗₁ σ⇒) ∘
        σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒                                                ≈⟨ (pullˡ (⟺ split₁ˡ) ⟩∘⟨ ⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
        ((((α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒) ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘
        σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇒                                                ≈⟨ extend² (⟺ serialize₂₁ ○ serialize₁₂) ⟩
        ((((α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒) ⊗₁ id ∘ α⇐) ∘ σ⇒ ⊗₁ id) ∘
        id ⊗₁ σ⇒ ∘ α⇐ ∘ id ⊗₁ α⇒                                                ≈˘⟨ pushʳ (refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity) ⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
        (((α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒) ⊗₁ id ∘ α⇐ ∘ σ⇒ ⊗₁ id ⊗₁ id) ∘
        (id ⊗₁ id) ⊗₁ σ⇒ ∘ α⇐ ∘ id ⊗₁ α⇒                                        ≈⟨ pushʳ assoc-commute-to ⟩∘⟨ extendʳ (⟺ assoc-commute-to) ⟩
        ((((α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒) ⊗₁ id ∘ (σ⇒ ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘
        α⇐ ∘ id ⊗₁ id ⊗₁ σ⇒ ∘ id ⊗₁ α⇒                                          ≈˘⟨ ((sym-assoc ○ sym-assoc) ⟩⊗⟨refl ○ split₁ˡ) ⟩∘⟨refl ⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩
        (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘
        α⇐ ∘ id ⊗₁ (id ⊗₁ σ⇒ ∘ α⇒)                                              ≈˘⟨ extend² (sym-assoc ○ pentagon-inv) ⟩
        (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ⊗₁ id) ∘ α⇐ ⊗₁ id) ∘
        (α⇐ ∘ id ⊗₁ α⇐) ∘ id ⊗₁ (id ⊗₁ σ⇒ ∘ α⇒)                                ≈˘⟨ split₁ˡ ⟩∘⟨ pushʳ split₂ˡ ⟩
        ((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id ∘
        α⇐ ∘ id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒)                                         ∎) ⟩⊗⟨refl ⟩∘⟨refl ⟩
      α⇒ ∘ (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id ∘ α⇐ ∘
        id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒)) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇐               ≈⟨ (refl⟩∘⟨ pushˡ ((sym-assoc ⟩⊗⟨refl) ○ split₁ˡ)) ⟩
      α⇒ ∘ (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id ∘ α⇐) ⊗₁ id ∘
      (id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒)) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇐                ≈⟨ (refl⟩∘⟨ split₁ˡ ⟩∘⟨ extendʳ (⟺ assoc-commute-to)) ○ pushʳ assoc ⟩
      (α⇒ ∘ (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id) ⊗₁ id) ∘
      α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ id ⊗₁ α⇐      ≈⟨ pushˡ assoc-commute-from ⟩
      ((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ (id ⊗₁ id) ∘ α⇒ ∘
      α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ id ⊗₁ α⇐      ≈˘⟨ refl⟩∘⟨ pullʳ (pullʳ (refl⟩∘⟨ split₂ˡ)) ⟩
      ((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ (id ⊗₁ id) ∘
      (α⇒ ∘ α⇐ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ ((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐)   ≈˘⟨ pullʳ (pullˡ (conjugate-from (α ∘ᵢ α ⊗ᵢ idᵢ) α pentagon)) ⟩
      (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ (id ⊗₁ id) ∘ α⇐) ∘
      id ⊗₁ α⇒ ∘ id ⊗₁ ((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐)                ≈⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟩∘⟨ ⟺ split₂ˡ ⟩
      (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id ∘ α⇐) ∘
      id ⊗₁ (α⇒ ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐)                      ≡⟨⟩
      (((α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id ∘ α⇐) ∘ id ⊗₁ j⇒   ≈˘⟨ switch-fromtoʳ α (switch-fromtoˡ α (⟺ hexagon₁))
                                                                                ⟩⊗⟨refl ⟩∘⟨refl ⟩∘⟨refl ⟩
      (σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ j⇒
    ∎) ⟩∘⟨refl ⟩
    α⇐ ∘ id ⊗₁ ((α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ j⇒) ∘ α⇒ ∘ α⇒       ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ id ⊗₁ j⇒ ∘ α⇒ ∘ α⇒   ≈˘⟨ pullʳ (pullʳ (extendʳ assoc-commute-from)) ⟩
    (α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒) ∘ (id ⊗₁ id) ⊗₁ j⇒ ∘ α⇒               ≡⟨⟩
    i⇒ ∘ (id ⊗₁ id) ⊗₁ j⇒ ∘ α⇒                                     ≈⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨ ⟺ swapInner-coherent ⟩∘⟨refl ⟩
    i⇒ ∘ id ⊗₁ i⇒ ∘ α⇒
  ∎

private
  mid-1-elim-coh : [ X ⊗₀ (unit ⊗₀ Y) ⇒ X ⊗₀ Y ]⟨ λ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ≈ id ⊗₁ λ⇒ ⟩
  mid-1-elim-coh = begin
    λ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐  ≈⟨ pullˡ (Kelly's.coherence₁ M) ⟩
    λ⇒ ⊗₁ id ∘ σ⇒ ⊗₁ id ∘ α⇐ ≈˘⟨  pushˡ split₁ˡ ⟩
    (λ⇒ ∘ σ⇒) ⊗₁ id ∘ α⇐     ≈⟨ braiding-coherence B ⟩⊗⟨refl ⟩∘⟨refl ⟩
    ρ⇒ ⊗₁ id ∘ α⇐             ≈˘⟨ switch-fromtoʳ α triangle ⟩
    id ⊗₁ λ⇒                  ∎

  Kelly₁′ :  [ unit ⊗₀ (X ⊗₀ Y) ⇒ X ⊗₀ Y ]⟨ λ⇒ ⊗₁ id ∘ α⇐ ≈ λ⇒ ⟩
  Kelly₁′ = ⟺ (switch-fromtoʳ α (Kelly's.coherence₁ M))

  Kelly₂′ : [  X ⊗₀ (Y ⊗₀ unit) ⇒ X ⊗₀ Y ]⟨ ρ⇒ ∘ α⇐ ≈ id ⊗₁ ρ⇒ ⟩
  Kelly₂′ = ⟺ (switch-fromtoʳ α (Kelly's.coherence₂ M))

  σ⁻¹-coherence : [ unit ⊗₀ X ⇒ X ]⟨ ρ⇒ ∘ σ⇒ ≈ λ⇒ ⟩
  σ⁻¹-coherence = inv-braiding-coherence (inv-Braided B)

swapInner-unitˡ : [ unit ⊗₀ (X ⊗₀ Y) ⇒ (X ⊗₀ Y) ]⟨
                    λ⇐ ⊗₁ id         ⇒⟨ (unit ⊗₀ unit) ⊗₀ (X ⊗₀ Y) ⟩
                    i⇒               ⇒⟨ (unit ⊗₀ X) ⊗₀ (unit ⊗₀ Y) ⟩
                    λ⇒ ⊗₁ λ⇒
                  ≈ λ⇒
                  ⟩
swapInner-unitˡ = begin
    λ⇒ ⊗₁ λ⇒ ∘ i⇒ ∘ λ⇐ ⊗₁ id      ≈⟨ refl⟩∘⟨ swapInner-coherent ⟩∘⟨ (Kelly's.coherence-inv₃ M ⟩⊗⟨refl) ⟩
    λ⇒ ⊗₁ λ⇒ ∘ j⇒ ∘ ρ⇐ ⊗₁ id      ≈⟨ pullˡ (pushˡ serialize₁₂) ⟩
    (λ⇒ ⊗₁ id ∘ id ⊗₁ λ⇒ ∘ α⇒ ∘ swapʳ ⊗₁ id ∘ α⇐) ∘ ρ⇐ ⊗₁ id
  ≈⟨ (refl⟩∘⟨ (begin
      id ⊗₁ λ⇒ ∘ α⇒ ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐  ≈⟨ pullˡ triangle ⟩
      ρ⇒ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐       ≈˘⟨ pushˡ split₁ˡ ⟩
      (ρ⇒ ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐             ≈⟨ (pullˡ Kelly₂′ ⟩⊗⟨refl ⟩∘⟨refl) ⟩
      (id ⊗₁ ρ⇒ ∘ id ⊗₁ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐            ≈˘⟨ pushˡ split₂ˡ ⟩⊗⟨refl ⟩∘⟨refl ⟩
      (id ⊗₁ (ρ⇒ ∘ σ⇒) ∘ α⇒) ⊗₁ id ∘ α⇐                ≈⟨ (refl⟩⊗⟨ σ⁻¹-coherence ⟩∘⟨refl) ⟩⊗⟨refl ⟩∘⟨refl ⟩
      (id ⊗₁ λ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐                        ≈⟨ triangle ⟩⊗⟨refl ⟩∘⟨refl ⟩
      (ρ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐                             ≈˘⟨ assoc-commute-to ⟩
      α⇐ ∘ ρ⇒ ⊗₁ (id ⊗₁ id)
    ∎)) ⟩∘⟨refl ⟩
    (λ⇒ ⊗₁ id ∘ α⇐ ∘ ρ⇒ ⊗₁ (id ⊗₁ id)) ∘ ρ⇐ ⊗₁ id   ≈⟨ (sym-assoc ○ (Kelly₁′ ⟩∘⟨ refl⟩⊗⟨ ⊗.identity)) ⟩∘⟨refl ⟩
    (λ⇒ ∘ ρ⇒ ⊗₁ id) ∘ ρ⇐ ⊗₁ id                       ≈⟨ cancelʳ (_≅_.isoʳ (unitorʳ ⊗ᵢ idᵢ)) ⟩
    λ⇒
  ∎

swapInner-unitʳ : [ (X ⊗₀ Y) ⊗₀ unit ⇒ (X ⊗₀ Y) ]⟨
                    id ⊗₁ λ⇐         ⇒⟨ (X ⊗₀ Y) ⊗₀ (unit ⊗₀ unit) ⟩
                    i⇒               ⇒⟨ (X ⊗₀ unit) ⊗₀ (Y ⊗₀ unit) ⟩
                    ρ⇒ ⊗₁ ρ⇒
                  ≈ ρ⇒
                  ⟩
swapInner-unitʳ = begin
    ρ⇒ ⊗₁ ρ⇒ ∘ i⇒ ∘ id ⊗₁ λ⇐                                  ≡⟨⟩
    ρ⇒ ⊗₁ ρ⇒ ∘ (α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒) ∘ id ⊗₁ λ⇐            ≈⟨ pullˡ (pushˡ serialize₂₁) ⟩
    (id ⊗₁ ρ⇒ ∘ ρ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒) ∘ id ⊗₁ λ⇐ ≈⟨ (refl⟩∘⟨ (begin
      ρ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒                                  ≈˘⟨ pushˡ (switch-fromtoʳ α triangle) ⟩
      id ⊗₁ λ⇒ ∘ id ⊗₁ swapˡ ∘ α⇒                                       ≈˘⟨ pushˡ split₂ˡ ⟩
      id ⊗₁ (λ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒                             ≈⟨ refl⟩⊗⟨ mid-1-elim-coh ⟩∘⟨refl ⟩
      id ⊗₁ (id ⊗₁ λ⇒) ∘ α⇒                                             ≈˘⟨ assoc-commute-from ⟩
      α⇒ ∘ (id ⊗₁ id) ⊗₁ λ⇒                                             ≈⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩
      α⇒ ∘ id ⊗₁ λ⇒                                                     ∎)) ⟩∘⟨refl ⟩
    (id ⊗₁ ρ⇒ ∘ α⇒ ∘ id ⊗₁ λ⇒) ∘ id ⊗₁ λ⇐                    ≈⟨ (sym-assoc ○ (Kelly's.coherence₂ M ⟩∘⟨refl )) ⟩∘⟨refl ⟩
    (ρ⇒ ∘ id ⊗₁ λ⇒) ∘ id ⊗₁ λ⇐                                ≈⟨ cancelʳ (_≅_.isoʳ (idᵢ ⊗ᵢ unitorˡ)) ⟩
    ρ⇒                                                         ∎

-- Two different ways of swapping things around are the same
private
  [23][14]ʳ : [ (X ⊗₀ Y) ⊗₀ (Z ⊗₀ W) ⇒ (Y ⊗₀ Z) ⊗₀ (X ⊗₀ W) ]⟨ α⇒ ∘ swapʳ ⊗₁ id ∘ (σ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐ ≈ (α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇒ ⊗₁ id ∘ α⇐ ⟩
  [23][14]ʳ = begin
    (α⇒ ∘ swapʳ ⊗₁ id ∘ (σ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐)  ≈˘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
    (α⇒ ∘ (swapʳ ∘ σ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐)        ≈⟨ refl⟩∘⟨ pullʳ (assoc ○ hexagon₁) ⟩⊗⟨refl ⟩∘⟨refl ⟩
    (α⇒ ∘ (α⇐ ∘ α⇒ ∘ σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐)       ≈⟨ refl⟩∘⟨ cancelˡ α.isoˡ ⟩⊗⟨refl ⟩∘⟨refl ⟩
    (α⇒ ∘ (σ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐)                 ≈⟨ extendʳ (pushʳ split₁ˡ) ⟩
    ((α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇒ ⊗₁ id ∘ α⇐)           ∎

  [13][42]ˡ : [ (X ⊗₀ Y) ⊗₀ (Z ⊗₀ W) ⇒ (X ⊗₀ Z)  ⊗₀ (W ⊗₀ Y) ]⟨ α⇐ ∘ id ⊗₁ (id ⊗₁ σ⇒) ∘ id ⊗₁ swapˡ ∘ α⇒ ≈ (α⇐ ∘ id ⊗₁ α⇒) ∘ id ⊗₁ σ⇒ ∘ α⇒ ⟩
  [13][42]ˡ = begin
    α⇐ ∘ id ⊗₁ (id ⊗₁ σ⇒) ∘ id ⊗₁ swapˡ ∘ α⇒         ≈˘⟨  refl⟩∘⟨ pushˡ split₂ˡ ⟩
    α⇐ ∘ id ⊗₁ (id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒ ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (⟺ assoc ○ (pullˡ (assoc ○ hexagon₁))) ⟩∘⟨refl ⟩
    α⇐ ∘ id ⊗₁ ((α⇒ ∘ σ⇒ ∘ α⇒) ∘ α⇐) ∘ α⇒            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ pullʳ (cancelʳ α.isoʳ) ⟩∘⟨refl ⟩
    α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒) ∘ α⇒                         ≈⟨ extendʳ (pushʳ split₂ˡ) ⟩
    (α⇐ ∘ id ⊗₁ α⇒) ∘ id ⊗₁ σ⇒ ∘ α⇒                  ∎

swapInner-braiding : [ (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ⇒ (Y ⊗₀ Z) ⊗₀ (W ⊗₀ X) ]⟨
                       i⇒         ⇒⟨ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z) ⟩
                       σ⇒ ⊗₁ σ⇒   ⇒⟨ (Y ⊗₀ W) ⊗₀ (Z ⊗₀ X) ⟩
                       i⇒
                     ≈ σ⇒
                     ⟩
swapInner-braiding = begin
    i⇒ ∘ σ⇒ ⊗₁ σ⇒ ∘ i⇒                                  ≡⟨⟩
    i⇒ ∘ σ⇒ ⊗₁ σ⇒ ∘ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒              ≈⟨ swapInner-coherent ⟩∘⟨ pushˡ serialize₁₂ ⟩
    j⇒ ∘ σ⇒ ⊗₁ id ∘ id ⊗₁ σ⇒ ∘ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒  ≈˘⟨ ((refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity) ⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl) ○ assoc ⟩
    ((α⇒ ∘ swapʳ ⊗₁ id ∘ α⇐) ∘ σ⇒ ⊗₁ (id ⊗₁ id)) ∘
    (id ⊗₁ id) ⊗₁ σ⇒ ∘ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒           ≈⟨ pullʳ (pullʳ assoc-commute-to) ⟩∘⟨ extendʳ (⟺ assoc-commute-to) ⟩
    (α⇒ ∘ swapʳ ⊗₁ id ∘ (σ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐) ∘
    α⇐ ∘ id ⊗₁ (id ⊗₁ σ⇒) ∘ id ⊗₁ swapˡ ∘ α⇒           ≈⟨ [23][14]ʳ ⟩∘⟨ [13][42]ˡ ⟩
    ((α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇒ ⊗₁ id ∘ α⇐) ∘ (α⇐ ∘ id ⊗₁ α⇒) ∘ id ⊗₁ σ⇒ ∘ α⇒  ≈˘⟨ extendʳ (pushʳ (pushʳ assoc)) ⟩
    (α⇒ ∘ σ⇒ ⊗₁ id) ∘ (α⇒ ⊗₁ id ∘ (α⇐ ∘ α⇐) ∘ id ⊗₁ α⇒) ∘ id ⊗₁ σ⇒ ∘ α⇒  ≈˘⟨ refl⟩∘⟨ switch-tofromˡ (α ⊗ᵢ idᵢ)
                                                                                (switch-tofromʳ (idᵢ ⊗ᵢ α) pentagon-inv) ⟩∘⟨refl ⟩
    (α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒               ≈⟨ pullʳ (sym-assoc ○ pullˡ hexagon₂) ⟩
    α⇒ ∘ ((α⇐ ∘ σ⇒) ∘ α⇐) ∘ α⇒                          ≈⟨ (refl⟩∘⟨ cancelʳ α.isoˡ) ⟩
    α⇒ ∘ (α⇐ ∘ σ⇒)                                       ≈⟨ cancelˡ α.isoʳ ⟩
    σ⇒                                                   ∎

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
