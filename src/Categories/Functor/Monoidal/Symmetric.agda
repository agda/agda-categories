{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal.Bundle
  using (SymmetricMonoidalCategory)

module Categories.Functor.Monoidal.Symmetric {o o′ ℓ ℓ′ e e′}
  (C : SymmetricMonoidalCategory o ℓ e) (D : SymmetricMonoidalCategory o′ ℓ′ e′)
  where

open import Level
open import Data.Product using (_,_)

open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal

private
  module C = SymmetricMonoidalCategory C renaming (braidedMonoidalCategory to B)
  module D = SymmetricMonoidalCategory D renaming (braidedMonoidalCategory to B)

import Categories.Functor.Monoidal.Braided C.B D.B as Braided

module Lax where
  open Braided.Lax

  -- Lax symmetric monoidal functors are just lax braided monoidal
  -- functors between symmetric monoidal categories.

  record SymmetricMonoidalFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      F                 : Functor C.U D.U
      isBraidedMonoidal : IsBraidedMonoidalFunctor F

    open Functor F public
    open IsBraidedMonoidalFunctor isBraidedMonoidal public

    monoidalFunctor : MonoidalFunctor C.monoidalCategory D.monoidalCategory
    monoidalFunctor = record { isMonoidal = isMonoidal }

module Strong where
  open Braided.Strong

  -- Strong symmetric monoidal functors are just strong braided
  -- monoidal functors between symmetric monoidal categories.

  record SymmetricMonoidalFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      F                 : Functor C.U D.U
      isBraidedMonoidal : IsBraidedMonoidalFunctor F

    open Functor F public
    open IsBraidedMonoidalFunctor isBraidedMonoidal public

    monoidalFunctor : StrongMonoidalFunctor C.monoidalCategory D.monoidalCategory
    monoidalFunctor = record { isStrongMonoidal = isStrongMonoidal }

    laxSymmetricMonoidalFunctor : Lax.SymmetricMonoidalFunctor
    laxSymmetricMonoidalFunctor = record
      { isBraidedMonoidal = isLaxBraidedMonoidal }
