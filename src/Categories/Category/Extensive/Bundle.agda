{-# OPTIONS --without-K --safe #-}

-- Bundled version of an extensive (distributive) Category
module Categories.Category.Extensive.Bundle where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Extensive using (Extensive)
open import Categories.Category.Distributive using (Distributive)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Extensive.Properties.Distributive using (Extensive×Cartesian⇒Distributive)

record ExtensiveCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U           : Category o ℓ e  -- U for underlying
    extensive   : Extensive U

  open Category U public
  open Extensive extensive public

-- Am extensive category with finite products
record ExtensiveDistributiveCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U           : Category o ℓ e  -- U for underlying
    extensive   : Extensive U
    cartesian   : Cartesian U

  open Category U public
  open Extensive extensive public
  open Distributive (Extensive×Cartesian⇒Distributive U extensive cartesian) public
