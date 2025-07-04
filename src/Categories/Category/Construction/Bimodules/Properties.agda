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
  open Monad using (C; T)
  open Bimodule using (F; actionˡ; actionʳ)
  open Bimodulehomomorphism f using (α; linearˡ; linearʳ)

  αisIso⇒fisIso : IsIso {C = hom (C M₁) (C M₂)} α → IsIso {C = Bimodules} f
  αisIso⇒fisIso αisIso = record
    { inv = record
      { α = α⁻¹
      ; linearˡ = linearˡ⁻¹
      ; linearʳ = linearʳ⁻¹
      }
    ; iso = record
      { isoˡ = IsIso.isoˡ αisIso
      ; isoʳ = IsIso.isoʳ αisIso
      }
    }
    where
      open hom.HomReasoning

      α⁻¹ : F B₂ ⇒₂ F B₁
      α⁻¹ = IsIso.inv αisIso

      αIso : F B₁ ≅ F B₂
      αIso = record
        { from = α
        ; to = α⁻¹
        ; iso = IsIso.iso αisIso
        }

      linearˡ⁻¹ : actionˡ B₁ ∘ᵥ α⁻¹ ◁ T M₁ ≈ α⁻¹ ∘ᵥ actionˡ B₂
      linearˡ⁻¹ = ⟺ (conjugate-from (αIso ◁ᵢ T M₁) αIso linearˡ)

      linearʳ⁻¹ : actionʳ B₁ ∘ᵥ T M₂ ▷ α⁻¹ ≈ α⁻¹ ∘ᵥ actionʳ B₂
      linearʳ⁻¹ = ⟺ (conjugate-from (T M₂ ▷ᵢ αIso) αIso linearʳ)

  αisIso⇒Iso : IsIso {C = hom (C M₁) (C M₂)} α → B₁ ≅ B₂
  αisIso⇒Iso αisIso = record
    { from = f
    ; to = IsIso.inv (αisIso⇒fisIso αisIso)
    ; iso = IsIso.iso (αisIso⇒fisIso αisIso)
    }
