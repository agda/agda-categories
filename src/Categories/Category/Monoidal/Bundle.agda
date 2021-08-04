{-# OPTIONS --without-K --safe #-}

-- Bundled version of Monoidal Category
module Categories.Category.Monoidal.Bundle where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

record MonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U        : Category o ℓ e
    monoidal : Monoidal U

  open Category U public
  open Monoidal monoidal public

record BraidedMonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U         : Category o ℓ e
    monoidal  : Monoidal U
    braided   : Braided monoidal

  monoidalCategory : MonoidalCategory o ℓ e
  monoidalCategory = record { U = U ; monoidal = monoidal }

  open Category U public
  open Braided braided public

record SymmetricMonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U         : Category o ℓ e
    monoidal  : Monoidal U
    symmetric : Symmetric monoidal

  open Category U public
  open Symmetric symmetric public

  braidedMonoidalCategory : BraidedMonoidalCategory o ℓ e
  braidedMonoidalCategory = record
    { U        = U
    ; monoidal = monoidal
    ; braided  = braided
    }

  open BraidedMonoidalCategory braidedMonoidalCategory public
    using (monoidalCategory)
