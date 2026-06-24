{-# OPTIONS --without-K --safe #-}
module Experiments.Functor.Exact where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Limits

open import Categories.Diagram.Limit
open import Categories.Diagram.Colimit

open import Categories.Category.Finite.Fin

private
  variable
    o ℓ e : Level
    𝒞 𝒟 ℐ : Category o ℓ e

LeftExact : (F : Functor 𝒞 𝒟) → Set _
LeftExact {𝒞 = 𝒞} F  = ∀ {shape : FinCatShape} {J : Functor (FinCategory shape) 𝒞} → (L : Limit J) → PreservesLimit F L

RightExact : (F : Functor 𝒞 𝒟) → Set _
RightExact {𝒞 = 𝒞} F  = ∀ {shape : FinCatShape} {J : Functor (FinCategory shape) 𝒞} → (L : Colimit J) → PreservesColimit F L

record Exact (F : Functor 𝒞 𝒟) : Set (levelOfTerm 𝒞 ⊔ levelOfTerm 𝒟) where
  field
    left-exact : LeftExact F
    right-exact : RightExact F
