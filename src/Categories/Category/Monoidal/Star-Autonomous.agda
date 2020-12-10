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
    Star : Functor Cᵒᵖ C

  open Functor Star renaming (op to Starₒₚ ; F₀ to Star₀)

  field
    FF-Star : FullyFaithful Star
    A≃A**  : id ≃ (Star ∘F Starₒₚ)
    𝒞[A⊗B,C*]≃𝒞[A,B⊗C*] : Hom[-,-] ∘F (⊗ₒₚ ⁂ Star) ≃ Hom[-,-] ∘F (id ⁂ (Star ∘F ⊗ₒₚ)) ∘F assocˡ _ _ _
