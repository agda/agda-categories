{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers
open import Categories.Bicategory.Monad

--- The construction of the tensorproduct is in ---
--- Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules and ---
--- Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms ---
--- but for almost all purposes you do not want to look at the construction there; ---
--- instead use the properties collected in this module. ---
module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Homomorphism
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ : Monad 𝒞}where

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands
open import Categories.Bicategory.Monad.Bimodule using (Bimodule)
open import Categories.Bicategory.Monad.Bimodule.Homomorphism using (Bimodulehomomorphism)
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Bimodule using (_⊗₀_; arr_⊗₀_)

import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Homomorphism.Core {𝒞 = 𝒞} {localCoeq} {M₁} {M₂} {M₃} as TensorproductOfHomomorphisms

private
  module HomCat {X} {Y} where
    open import Categories.Morphism (hom X Y) public using (Epi)
    open import Categories.Diagram.Coequalizer (hom X Y) public using (Coequalizer; Coequalizer⇒Epi)

open HomCat

open Bimodulehomomorphism using (α)

--- The names follow the scheme ---
--- [property]_⊗₁_ ---
--- This makes it look like '[propery h₂ ⊗₁ h₁]' is a field of the record entry 'h₂ ⊗₁ h₁'. ---
--- Whenever 'field h₂ ⊗₀ h₁' is an actual field of 'h₂ ⊗₀ h₁', ---
--- then 'fieldDef h₂ ⊗₀ h₁' indicates the property that is defining for that field. ---

infixl 30 _⊗₁_
            
_⊗₁_ : {B₂ B'₂ : Bimodule M₂ M₃} {B₁ B'₁ : Bimodule M₁ M₂}
    → Bimodulehomomorphism B₂ B'₂ → Bimodulehomomorphism B₁ B'₁ → Bimodulehomomorphism (B₂ ⊗₀ B₁) (B'₂ ⊗₀ B'₁)
h₂ ⊗₁ h₁ = h₂⊗h₁
  where
    open TensorproductOfHomomorphisms h₂ h₁ using (h₂⊗h₁)
      
--- We are hiding all definitions behind an abstract clause because we think no one will ever want to know how these are defined. ---
abstract

  --- The following property is defining for the underlying 2-cell of l ⊗₁ r ---
  αDef_⊗₁_ : {B₂ B'₂ : Bimodule M₂ M₃} {B₁ B'₁ : Bimodule M₁ M₂}
             (h₂ : Bimodulehomomorphism B₂ B'₂) (h₁ : Bimodulehomomorphism B₁ B'₁)
           → (arr B'₂ ⊗₀ B'₁) ∘ᵥ α h₂ ⊚₁ α h₁ ≈ α (h₂ ⊗₁ h₁) ∘ᵥ (arr B₂ ⊗₀ B₁)
  αDef h₂ ⊗₁ h₁ = αSq
    where
      open TensorproductOfHomomorphisms h₂ h₁ using (αSq)
