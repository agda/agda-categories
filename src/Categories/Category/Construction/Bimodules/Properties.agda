{-# OPTIONS --without-K --safe #-}


open import Categories.Bicategory
open import Categories.Bicategory.Monad

module Categories.Category.Construction.Bimodules.Properties
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {M₁ M₂ : Monad 𝒞} where

open import Agda.Primitive

import Categories.Category.Construction.Bimodules
open import Categories.Category

Bimodules : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
Bimodules = Categories.Category.Construction.Bimodules.Bimodules M₁ M₂

private
  module Cat {o₁ ℓ₁ e₁} {C : Categories.Category.Category o₁ ℓ₁ e₁} where
    open Categories.Category.Category C using (Obj; _⇒_) public
    open import Categories.Morphism C using (IsIso; _≅_) public
    open import Categories.Morphism.Reasoning.Iso C using (conjugate-from) public

open Cat


import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞 using (hom; _⇒₂_; _≈_; _∘ᵥ_; _◁_; _▷_; _◁ᵢ_; _▷ᵢ_)

open import Categories.Bicategory.Monad.Bimodule {𝒞 = 𝒞}
open import Categories.Bicategory.Monad.Bimodule.Homomorphism {𝒞 = 𝒞}

module Bimodulehom-isIso {B₁ B₂ : Obj {C = Bimodules}} (f : _⇒_ {C = Bimodules} B₁ B₂) where
  open Monad M₁ using () renaming (C to C₁; T to T₁)
  open Monad M₂ using () renaming (C to C₂; T to T₂)
  open Bimodule B₁ using () renaming (F to F₁; actionˡ to actionˡ₁)
  open Bimodule B₂ using () renaming (F to F₂; actionˡ to actionˡ₂)
  open Bimodulehomomorphism f using (α; linearˡ; linearʳ)

  αisIso⇒fisIso : IsIso {C = hom C₁ C₂} α → IsIso {C = Bimodules} f
  αisIso⇒fisIso αisIso = record
    { inv = record
      { α = α⁻¹
        -- F₂ ⇒₂ F₁
      ; linearˡ = ⟺ (conjugate-from (αIso ◁ᵢ T₁) αIso linearˡ)
        -- linearˡ : actionˡ₁ ∘ᵥ α⁻¹ ◁ T₁ ≈ α⁻¹ ∘ᵥ actionˡ₂
      ; linearʳ = ⟺ (conjugate-from (T₂ ▷ᵢ αIso) αIso linearʳ)
      -- linearʳ : actionʳ₁ ∘ᵥ T₂ ▷ α⁻¹ ≈ α⁻¹ ∘ᵥ actionʳ₂
      }
    ; iso = record
      { isoˡ = IsIso.isoˡ αisIso
      ; isoʳ = IsIso.isoʳ αisIso
      }
    }
    where
      open hom.HomReasoning
      α⁻¹ = IsIso.inv αisIso
      αIso : F₁ ≅ F₂
      αIso = record
        { from = α
        ; to = α⁻¹
        ; iso = IsIso.iso αisIso
        }

  αisIso⇒Iso : IsIso {C = hom C₁ C₂} α → B₁ ≅ B₂
  αisIso⇒Iso αisIso = record
    { from = f
    ; to = IsIso.inv (2cellisIso⇒isIso αisIso)
    ; iso = IsIso.iso (2cellisIso⇒isIso αisIso)
    }
