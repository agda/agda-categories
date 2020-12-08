{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric

module Categories.Category.Monoidal.Star-Autonomous {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Level

open import Categories.Category.Product
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Morphism C
open import Categories.Functor.Hom
open Hom C

open Category C renaming (op to Cᵒᵖ) hiding (id)
open Monoidal M
open Functor ⊗ renaming (op to ⊗ₒₚ)

open import Relation.Binary.Structures

record Star-Autonomous : Set (levelOfTerm M) where
  field
    symmetric : Symmetric M
    F⁻¹ : Functor Cᵒᵖ C

  open Functor F⁻¹ renaming (op to F⁻¹ₒₚ ; F₀ to F⁻¹₀)

  field
    FFF⁻¹ : FullyFaithful F⁻¹
    A≃A⁻¹⁻¹ : id ≃ (F⁻¹ ∘F F⁻¹ₒₚ)
    𝒞[A⊗B,C⁻¹]≃𝒞[A,B⊗C⁻¹] : Hom[-,-] ∘F (⊗ₒₚ ⁂ F⁻¹) ≃ Hom[-,-] ∘F (id ⁂ (F⁻¹ ∘F ⊗ₒₚ)) ∘F assocˡ _ _ _
