{-# OPTIONS --without-K --safe #-}

-- Bundled version of a Cartesian Closed Category
module Categories.Category.CartesianClosed.Bundle where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Cartesian.Bundle

record CartesianClosedCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U         : Category o ℓ e  -- U for underlying
    cartesianClosed : CartesianClosed U

  open Category U public

  cartesianCategory : CartesianCategory o ℓ e
  cartesianCategory = record
    { U = U
    ; cartesian = CartesianClosed.cartesian cartesianClosed
    }
