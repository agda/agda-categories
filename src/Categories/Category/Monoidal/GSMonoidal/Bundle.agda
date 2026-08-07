{-# OPTIONS --without-K --safe #-}

-- Bundled version of a GS-monoidal category.

module Categories.Category.Monoidal.GSMonoidal.Bundle where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.GSMonoidal using (GSMonoidal)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

record GSMonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U          : Category o ℓ e  -- U for underlying
    monoidal   : Monoidal U
    symmetric  : Symmetric monoidal
    gsMonoidal : GSMonoidal symmetric

  symmetricMonoidalCategory : SymmetricMonoidalCategory o ℓ e
  symmetricMonoidalCategory = record { symmetric = symmetric }

  open Category U public
  open Symmetric symmetric public
  open GSMonoidal gsMonoidal public

  open SymmetricMonoidalCategory symmetricMonoidalCategory public
    using (monoidalCategory; braidedMonoidalCategory)
