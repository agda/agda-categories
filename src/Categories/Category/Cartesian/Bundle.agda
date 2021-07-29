{-# OPTIONS --without-K --safe #-}

-- Bundled version of a Cartesian Category
module Categories.Category.Cartesian.Bundle where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Cartesian using (Cartesian; module CartesianMonoidal)
open import Categories.Category.Monoidal using (MonoidalCategory)

record CartesianCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U         : Category o ℓ e  -- U for underlying
    cartesian : Cartesian U

  open Category U public
  open Cartesian cartesian public

  monoidalCategory : MonoidalCategory o ℓ e
  monoidalCategory = record
    { U        = U
    ; monoidal = CartesianMonoidal.monoidal U cartesian
    }
