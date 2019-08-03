{-# OPTIONS --without-K --safe #-}
module Categories.Comonad where

open import Level

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor; id; _∘F_)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)
open import Categories.NaturalTransformation.Equivalence
open NaturalIsomorphism

record Comonad {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : Endofunctor C
    ε : NaturalTransformation F id
    δ : NaturalTransformation F (F ∘F F)

  open Functor F

  field
    assoc     : F⇒G (associator F F F) ∘ᵥ (δ ∘ʳ F) ∘ᵥ δ ≃ (F ∘ˡ δ) ∘ᵥ δ
    identityˡ : F⇒G unitorʳ ∘ᵥ (F ∘ˡ ε) ∘ᵥ δ ≃ idN
    identityʳ : F⇒G unitorˡ ∘ᵥ (ε ∘ʳ F) ∘ᵥ δ ≃ idN
