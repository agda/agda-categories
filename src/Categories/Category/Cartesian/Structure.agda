{-# OPTIONS --without-K --safe #-}

-- here we define the structure version of a cartesian category
module Categories.Category.Cartesian.Structure where

open import Level

open import Categories.Category
open import Categories.Category.Cartesian
open import Categories.Category.Monoidal

record CartesianCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U         : Category o ℓ e  -- U for underlying
    cartesian : Cartesian U

  module U = Category U
  module cartesian = Cartesian cartesian

  open U public
  open cartesian public

  monoidalCategory : MonoidalCategory o ℓ e
  monoidalCategory = record
    { U        = U
    ; monoidal = monoidal
    }
