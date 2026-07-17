{-# OPTIONS --without-K --safe #-}

-- Bundled version of Monoidal Category
module Categories.Category.Monoidal.Bundle where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Properties using (monoidal-Op)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Braided.Properties using (braided-Op)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Symmetric.Properties using (symmetric-Op)

record MonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U        : Category o ℓ e
    monoidal : Monoidal U

  open Category U hiding (op) public
  open Monoidal monoidal public

  op : MonoidalCategory o ℓ e
  op = record { monoidal = monoidal-Op monoidal }

record BraidedMonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U         : Category o ℓ e
    monoidal  : Monoidal U
    braided   : Braided monoidal

  monoidalCategory : MonoidalCategory o ℓ e
  monoidalCategory = record { monoidal = monoidal }

  open Category U hiding (op) public
  open Braided braided public

  op : BraidedMonoidalCategory o ℓ e
  op = record { braided = braided-Op braided }

record SymmetricMonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U         : Category o ℓ e
    monoidal  : Monoidal U
    symmetric : Symmetric monoidal

  open Category U hiding (op) public
  open Symmetric symmetric public

  braidedMonoidalCategory : BraidedMonoidalCategory o ℓ e
  braidedMonoidalCategory = record { braided = braided }

  open BraidedMonoidalCategory braidedMonoidalCategory public
    using (monoidalCategory)

  op : SymmetricMonoidalCategory o ℓ e
  op = record { symmetric = symmetric-Op symmetric }
