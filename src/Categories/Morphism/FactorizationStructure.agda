{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Morphism.Lifts using (MorphismClass)

module Categories.Morphism.FactorizationStructure where


private
  variable
    o ℓ e ℓℰ ℓℳ : Level
    𝒞 : Category o ℓ e

open import Categories.Morphism.FactorizationStructure.Core

FactorizationStructure-syntax : (𝒞 : Category o ℓ e) → MorphismClass 𝒞 ℓℰ → MorphismClass 𝒞 ℓℳ → Set (o ⊔ ℓ ⊔ e ⊔ ℓℰ ⊔ ℓℳ)
FactorizationStructure-syntax 𝒞 ℰ ℳ = FactorizationStructure 𝒞 ℰ ℳ

syntax FactorizationStructure-syntax 𝒞 ℰ ℳ = [ ℰ , ℳ ]-structured 𝒞




