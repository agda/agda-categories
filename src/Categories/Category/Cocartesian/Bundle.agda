{-# OPTIONS --without-K --safe #-}

-- Bundled version of a Cocartesian Category
module Categories.Category.Cocartesian.Bundle where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Cocartesian using (Cocartesian)

record CocartesianCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U           : Category o ℓ e  -- U for underlying
    cocartesian : Cocartesian U

  open Category U public
  open Cocartesian cocartesian public
