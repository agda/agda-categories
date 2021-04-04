{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Structure where

open import Level

open import Categories.Category
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Symmetric

record MonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U        : Category o ℓ e
    monoidal : Monoidal U

  module U = Category U
  module monoidal = Monoidal monoidal

  open U public
  open monoidal public

record SymmetricMonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U         : Category o ℓ e
    monoidal  : Monoidal U
    symmetric : Symmetric monoidal

  module U = Category U
  module monoidal = Monoidal monoidal
  module symmetric = Symmetric symmetric

  monoidalCategory : MonoidalCategory o ℓ e
  monoidalCategory = record { U = U ; monoidal = monoidal }

  open U public
  open symmetric public
