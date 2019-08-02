{-# OPTIONS --without-K --safe #-}
module Categories.Monad where

open import Level

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor; id; _∘F_)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)
open import Categories.NaturalTransformation.Equivalence
open NaturalIsomorphism

record Monad {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : Endofunctor C
    η : NaturalTransformation id F
    μ : NaturalTransformation (F ∘F F) F

  open Functor F

  field
    assoc     : μ ∘ᵥ (F ∘ˡ μ) ∘ᵥ (F⇒G (associator F F F)) ≃ μ ∘ᵥ (μ ∘ʳ F)
    identityˡ : μ ∘ᵥ (F ∘ˡ η) ∘ᵥ (F⇐G unitorʳ) ≃ idN
    identityʳ : μ ∘ᵥ (η ∘ʳ F) ∘ᵥ (F⇐G unitorˡ) ≃ idN
