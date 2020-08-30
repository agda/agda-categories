{-# OPTIONS --without-K --safe #-}

-- here we define the structure version of a cartesian category
module Categories.Category.Cartesian.Structure where

open import Level

open import Categories.Category
open import Categories.Category.Cartesian

record CartesianCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    𝒞 : Category o ℓ e
    cartesian : Cartesian 𝒞

  module 𝒞 = Category 𝒞
  module cartesian = Cartesian cartesian

  open 𝒞 public
  open cartesian public
