{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers
open import Categories.Bicategory.Monad

--- The construction of the tensorproduct is in ---
--- Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules and ---
--- Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms ---
--- but for almost all purposes you do not want to look at the construction there; ---
--- instead use the properties collected in this module. ---
module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Bimodule
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ : Monad 𝒞}where

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands
open import Categories.Bicategory.Monad.Bimodule using (Bimodule)

import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Bimodule.Core {𝒞 = 𝒞} {localCoeq} {M₁} {M₂} {M₃} as TensorproductOfBimodules

private
  module HomCat {X} {Y} where
    open import Categories.Morphism (hom X Y) public using (Epi)
    open import Categories.Diagram.Coequalizer (hom X Y) public using (Coequalizer; Coequalizer⇒Epi)

open HomCat

open Monad using (T)
open Bimodule using (F; actionˡ; actionʳ)

--- The names follow the scheme ---
--- [property]_⊗₀_ ---
--- This makes it look like '[propery] B₂ ⊗₀ B₁' is a field of the record entry 'B₂ ⊗₀ B₁'. ---
--- Whenever 'field B₂ ⊗₀ B₁' is an actual field of 'B₂ ⊗₀ B₁', ---
--- then 'fieldDef B₂ ⊗₀ B₁' indicates the property that is defining for that field. ---

infixl 30 _⊗₀_
            
--- Tensorproduct of Bimodules ---
_⊗₀_ : Bimodule M₂ M₃ → Bimodule M₁ M₂ → Bimodule M₁ M₃
B₂ ⊗₀ B₁ = B₂⊗B₁
  where
    open TensorproductOfBimodules B₂ B₁ using (B₂⊗B₁)

--- We are hiding all definitions behind an abstract clause because we think no one will ever want to know how these are defined. ---
abstract
  arr_⊗₀_ : (B₂ : Bimodule M₂ M₃) (B₁ : Bimodule M₁ M₂) → (F B₂ ∘₁ F B₁) ⇒₂ F (B₂ ⊗₀ B₁)
  arr B₂ ⊗₀ B₁ = Coequalizer.arr B₂⦃M₂⦄B₁
    where
      open TensorproductOfBimodules B₂ B₁ using (B₂⦃M₂⦄B₁)

  epi_⊗₀_ : (B₂ : Bimodule M₂ M₃) (B₁ : Bimodule M₁ M₂) → Epi (arr B₂ ⊗₀ B₁)
  epi B₂ ⊗₀ B₁ = Coequalizer⇒Epi B₂⦃M₂⦄B₁
    where
      open TensorproductOfBimodules B₂ B₁ using (B₂⦃M₂⦄B₁)

  --- The following property is defining for the left-action of B₂ ⊗₀ B₁ ---
  actionˡDef_⊗₀_ : (B₂ : Bimodule M₂ M₃) (B₁ : Bimodule M₁ M₂)
                → (arr B₂ ⊗₀ B₁) ∘ᵥ F B₂ ▷ actionˡ B₁ ∘ᵥ α⇒ ≈ actionˡ (B₂ ⊗₀ B₁) ∘ᵥ arr B₂ ⊗₀ B₁ ◁ T M₁
  actionˡDef B₂ ⊗₀ B₁ = actionˡSq
    where
      open TensorproductOfBimodules.Left-Action B₂ B₁ using (actionˡSq)

  --- The following property is defining for the right-action of B₂ ⊗₀ B₁ ---
  actionʳDef_⊗₀_ : (B₂ : Bimodule M₂ M₃) (B₁ : Bimodule M₁ M₂)
                → (arr B₂ ⊗₀ B₁) ∘ᵥ actionʳ B₂ ◁ F B₁ ∘ᵥ α⇐ ≈ actionʳ (B₂ ⊗₀ B₁) ∘ᵥ T M₃ ▷ arr B₂ ⊗₀ B₁
  actionʳDef B₂ ⊗₀ B₁ = actionʳSq
    where
      open TensorproductOfBimodules.Right-Action B₂ B₁ using (actionʳSq)
