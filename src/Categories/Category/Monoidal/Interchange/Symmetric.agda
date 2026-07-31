{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Extra identities that hold only for symmetric monoidal categories.

module Categories.Category.Monoidal.Interchange.Symmetric
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (S : Symmetric M) where

open import Data.Product using (_,_)

import Categories.Category.Construction.Core C as Core
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
open import Categories.Category.Monoidal.Interchange using (HasInterchange)
import Categories.Category.Monoidal.Interchange.Braided as BraidedInterchange
  using (module swapInner; swapInner-braiding; swapInner-unitˡ)
import Categories.Category.Monoidal.Reasoning M as MonoidalReasoning
import Categories.Category.Monoidal.Utilities M as MonoidalUtilities
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (_≃_; niHelper)
open import Categories.Morphism.IsoEquiv C using (from-unique; to-unique)
open import Categories.Morphism.Reasoning C
  using (elim-center; pushˡ; pullʳ; cancelʳ; cancelInner; switch-fromtoˡ)

open Category C
open Commutation C
open MonoidalReasoning
open MonoidalUtilities using (_⊗ᵢ_)
open Symmetric S renaming (associator to α; braided to B)
open BraidedInterchange B
open Core.Shorthands               -- for idᵢ, _∘ᵢ_, ...
open MonoidalUtilities.Shorthands  -- for λ⇒, ρ⇒, α⇒, ...
open BraidedProps.Shorthands B     -- for σ⇒, ...

private
  variable
    W W₁ W₂ X X₁ X₂ Y Y₁ Y₂ Z Z₁ Z₂ : Obj
    f g h i : X ⇒ Y

private
  i⇒ = swapInner.from
  i⇐ = swapInner.to

swapInner-commutative : [ (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ⇒
                          (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ]⟨
                           i⇒    ⇒⟨ (X₁ ⊗₀ Y₁) ⊗₀ (X₂ ⊗₀ Y₂) ⟩
                           i⇒
                        ≈ id
                        ⟩
swapInner-commutative = begin
    i⇒ ∘ i⇒                                                               ≈⟨ pullʳ (cancelInner α.isoʳ) ⟩
    α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒  ≈˘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    α⇐ ∘ id ⊗₁ ((α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (∘-resp-≈ʳ sym-assoc ○ α[σ⊗1]α⁻¹.isoʳ) ⟩∘⟨refl ⟩
    α⇐ ∘ id ⊗₁ id ∘ α⇒                                                    ≈⟨ elim-center ⊗.identity ○ α.isoˡ ⟩
    id                                                                     ∎
  where module α[σ⊗1]α⁻¹ = _≅_ (α ∘ᵢ braided-iso ⊗ᵢ idᵢ ∘ᵢ α ⁻¹) using (isoʳ)

swapInner-iso : (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ≅ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z)
swapInner-iso = record
  { from = i⇒
  ; to   = i⇒
  ; iso  = record
    { isoˡ = swapInner-commutative
    ; isoʳ = swapInner-commutative
    }
  }

swapInner-selfInverse : [ (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ⇒
                          (X₁ ⊗₀ Y₁) ⊗₀ (X₂ ⊗₀ Y₂) ]⟨
                          i⇒
                        ≈ i⇐
                        ⟩
swapInner-selfInverse =
  to-unique (iso swapInner-iso) swapInner.iso Equiv.refl

abstract
  swapInner-unitˡ⁻¹ : [ X ⊗₀ Y ⇒ unit ⊗₀ (X ⊗₀ Y) ]⟨
                        λ⇐ ⊗₁ λ⇐  ⇒⟨ (unit ⊗₀ X) ⊗₀ (unit ⊗₀ Y) ⟩
                        i⇒        ⇒⟨ (unit ⊗₀ unit) ⊗₀ (X ⊗₀ Y) ⟩
                        λ⇒ ⊗₁ id
                      ≈ λ⇐
                      ⟩
  swapInner-unitˡ⁻¹ {X} {Y} = from-unique (iso unit-insert) (iso (unitorˡ ⁻¹)) unit-remove
    where
    split-units : X ⊗₀ Y ≅ (unit ⊗₀ X) ⊗₀ (unit ⊗₀ Y)
    split-units = (unitorˡ ⁻¹) ⊗ᵢ (unitorˡ ⁻¹)

    join-units : (unit ⊗₀ unit) ⊗₀ (X ⊗₀ Y) ≅ unit ⊗₀ (X ⊗₀ Y)
    join-units = unitorˡ ⊗ᵢ idᵢ

    unit-insert : X ⊗₀ Y ≅ unit ⊗₀ (X ⊗₀ Y)
    unit-insert = join-units ∘ᵢ swapInner-iso ∘ᵢ split-units

    module unit-insert = _≅_ unit-insert

    unit-remove : [ unit ⊗₀ (X ⊗₀ Y) ⇒ X ⊗₀ Y ]⟨ unit-insert.to ≈ λ⇒ ⟩
    unit-remove = assoc ○ swapInner-unitˡ

swapInner-braiding′ : [ (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ⇒ (Y ⊗₀ W) ⊗₀ (Z ⊗₀ X) ]⟨
                        i⇒         ⇒⟨ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z) ⟩
                        σ⇒ ⊗₁ σ⇒
                      ≈ σ⇒         ⇒⟨ (Y ⊗₀ Z) ⊗₀ (W ⊗₀ X) ⟩
                        i⇒
                      ⟩
swapInner-braiding′ = switch-fromtoˡ swapInner-iso swapInner-braiding

swapInner-braidingˡ : [ (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ⇒ (Y ⊗₀ W) ⊗₀ (X ⊗₀ Z) ]⟨
                        i⇒         ⇒⟨ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z) ⟩
                        σ⇒ ⊗₁ id
                      ≈ σ⇒         ⇒⟨ (Y ⊗₀ Z) ⊗₀ (W ⊗₀ X) ⟩
                        i⇒         ⇒⟨ (Y ⊗₀ W) ⊗₀ (Z ⊗₀ X) ⟩
                        id ⊗₁ σ⇒
                      ⟩
swapInner-braidingˡ = begin
  (σ⇒ ⊗₁ id) ∘ i⇒                 ≈˘⟨ refl⟩⊗⟨ commutative ⟩∘⟨refl ⟩
  (σ⇒ ⊗₁ (σ⇒ ∘ σ⇒)) ∘ i⇒          ≈⟨ split₂ˡ ⟩∘⟨refl ⟩
  ((id ⊗₁ σ⇒) ∘ (σ⇒ ⊗₁ σ⇒)) ∘ i⇒  ≈⟨ pullʳ swapInner-braiding′ ⟩
  (id ⊗₁ σ⇒) ∘ i⇒ ∘ σ⇒            ∎

swapInner-braidingʳ : [ (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ⇒ (X ⊗₀ Z) ⊗₀ (W ⊗₀ Y) ]⟨
                        i⇒         ⇒⟨ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z) ⟩
                        σ⇒
                      ≈ σ⇒ ⊗₁ σ⇒  ⇒⟨ (X ⊗₀ W) ⊗₀ (Z ⊗₀ Y) ⟩
                        i⇒
                      ⟩
swapInner-braidingʳ = begin
  σ⇒ ∘ i⇒                       ≈˘⟨ swapInner-braiding ⟩∘⟨refl ⟩
  (i⇒ ∘ (σ⇒ ⊗₁ σ⇒ ∘ i⇒)) ∘ i⇒   ≈⟨ pullʳ (cancelʳ swapInner-commutative) ⟩
  i⇒ ∘ (σ⇒ ⊗₁ σ⇒)               ∎
