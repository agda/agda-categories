{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
module Categories.Object.InternalRelation {o ℓ e} (𝒞 : CartesianCategory o ℓ e) where

open import Level
open import Data.Product hiding (_×_)
open import Data.Unit

open import Categories.Category
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
open import Categories.Morphism.Notation

𝒞′ = CartesianCategory.U 𝒞

open import Categories.Category.BinaryProducts 𝒞′
open import Categories.Category.Cartesian 𝒞′

private
  module 𝒞′ = Category 𝒞′
  module 𝒞 = CartesianCategory 𝒞

open BinaryProducts (Cartesian.products (CartesianCategory.cartesian 𝒞))
  using (_×_; product; π₁; π₂; ⟨_,_⟩)

BinaryRelation : 𝒞.Obj → 𝒞.Obj → Set (o ⊔ ℓ ⊔ e)
BinaryRelation X Y = Σ[ Z ∈ 𝒞.Obj ](Z ↣ (X × Y)) where open Mor 𝒞′; open _↣_

record EquivalenceRelation (X : 𝒞.Obj) : Set (o ⊔ ℓ ⊔ e) where
  open Category 𝒞′
  open Mor 𝒞′
  open _↣_

  field
    relation : BinaryRelation X X

  R    = proj₁ relation
  incl = proj₂ relation

  field
    refl  : X ⇒ R
    sym   : R ⇒ R
    trans : R × R ⇒ R
    
    is-refl₁ : π₁ ∘ (mor incl) ∘ refl ≈ id 
    is-refl₂ : π₂ ∘ (mor incl) ∘ refl ≈ id 

    is-sym₁ : π₁ ∘ (mor incl) ∘ sym ≈ π₂ ∘ (mor incl) 
    is-sym₂ : π₂ ∘ (mor incl) ∘ sym ≈ π₁ ∘ (mor incl)

    -- is-trans₁ : -- 𝒞 must have pullbacks
    -- is-trans₂ : -- 𝒞 must have pullbacks
