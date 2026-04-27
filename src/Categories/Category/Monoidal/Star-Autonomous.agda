{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Category.Monoidal.Star-Autonomous {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Level

open import Categories.Category.Product using (_×₁_; assocˡ)
open import Categories.Functor using (Functor; _∘F_; id)
open import Categories.Functor.Properties using (FullyFaithful)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Functor.Hom

open Category C renaming (op to Cᵒᵖ) hiding (id)
open Monoidal M
open Functor ⊗ renaming (op to ⊗ₒₚ)
open Hom C

record Star-Autonomous : Set (levelOfTerm M) where
  field
    symmetric : Symmetric M
    Star : Functor Cᵒᵖ C

  open Functor Star renaming (op to Starₒₚ) public

  field
    FF-Star : FullyFaithful Star
    A**≃A  : (Star ∘F Starₒₚ) ≃ id
    𝒞[A⊗B,C*]≃𝒞[A,B⊗C*] : Hom[-,-] ∘F (⊗ₒₚ ×₁ Star) ≃ Hom[-,-] ∘F (id ×₁ (Star ∘F ⊗ₒₚ)) ∘F assocˡ _ _ _
