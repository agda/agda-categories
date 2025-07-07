{-# OPTIONS --without-K --safe #-}


open import Categories.Bicategory
open import Categories.Bicategory.Monad

module Categories.Category.Construction.Bimodules.Properties
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {M₁ M₂ : Monad 𝒞} where

open import Categories.Bicategory.Monad.Bimodule using (Bimodule)
open import Categories.Bicategory.Monad.Bimodule.Homomorphism using (Bimodulehomomorphism)
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning.Iso as IsoReasoning

private
  module Bimodules where
    open import Categories.Category.Construction.Bimodules M₁ M₂ using (Bimodules)
    open import Categories.Category using (Category)
    open Category Bimodules public
    open Mor Bimodules using (IsIso; _≅_) public

  module 𝒞 where
    import Categories.Bicategory.Extras as Bicat
    open Bicat 𝒞 public

  module HomCat {A B : 𝒞.Obj} where
    open Mor (𝒞.hom A B) using (IsIso; _≅_) public
    open IsoReasoning (𝒞.hom A B) using (conjugate-from) public

module Bimodule-Isomorphism {B₁ B₂ : Bimodules.Obj} (f : B₁ Bimodules.⇒ B₂) where
  open Monad using (C; T)
  open Bimodule using (F; actionˡ; actionʳ)
  open Bimodulehomomorphism f using (α; linearˡ; linearʳ)

  αisIso⇒fisIso : HomCat.IsIso α → Bimodules.IsIso f
  αisIso⇒fisIso αisIso = record
    { inv = record
      { α = α⁻¹
      ; linearˡ = linearˡ⁻¹
      ; linearʳ = linearʳ⁻¹
      }
    ; iso = record
    -- Cannot be delta reduced because of size issues
      { isoˡ = HomCat.IsIso.isoˡ αisIso
      ; isoʳ = HomCat.IsIso.isoʳ αisIso
      }
    }
    where
      open 𝒞.hom.HomReasoning

      α⁻¹ : F B₂ 𝒞.⇒₂ F B₁
      α⁻¹ = HomCat.IsIso.inv αisIso

      αIso : F B₁ HomCat.≅ F B₂
      αIso = record
        { from = α
        ; to = α⁻¹
        ; iso = HomCat.IsIso.iso αisIso
        }

      linearˡ⁻¹ : actionˡ B₁ 𝒞.∘ᵥ α⁻¹ 𝒞.◁ T M₁ 𝒞.≈ α⁻¹ 𝒞.∘ᵥ actionˡ B₂
      linearˡ⁻¹ = ⟺ (HomCat.conjugate-from (αIso 𝒞.◁ᵢ T M₁) αIso linearˡ)

      linearʳ⁻¹ : actionʳ B₁ 𝒞.∘ᵥ T M₂ 𝒞.▷ α⁻¹ 𝒞.≈ α⁻¹ 𝒞.∘ᵥ actionʳ B₂
      linearʳ⁻¹ = ⟺ (HomCat.conjugate-from (T M₂ 𝒞.▷ᵢ αIso) αIso linearʳ)

  αisIso⇒Iso : HomCat.IsIso α → B₁ Bimodules.≅ B₂
  αisIso⇒Iso αisIso = record
    { from = f
    ; to = Bimodules.IsIso.inv (αisIso⇒fisIso αisIso)
    ; iso = Bimodules.IsIso.iso (αisIso⇒fisIso αisIso)
    }
