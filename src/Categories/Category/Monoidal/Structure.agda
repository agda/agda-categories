{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Structure where

open import Level

open import Categories.Category
open import Categories.Category.Monoidal.Core

record MonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U        : Category o ℓ e
    monoidal : Monoidal U

  module U = Category U
  module monoidal = Monoidal monoidal

  open U public
  open monoidal public
