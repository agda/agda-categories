{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Monoidal.Symmetric.Properties where

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor.Monoidal.Braided.Properties
  using (idF-IsBraidedMonoidal; idF-IsStrongBraidedMonoidal; ∘-IsBraidedMonoidal; ∘-IsStrongBraidedMonoidal)
open import Categories.Functor.Monoidal.Symmetric using (module Lax; module Strong)
open import Level

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ e e′ e″ : Level

-- The identity functor is symmetric monoidal

module _ (C : SymmetricMonoidalCategory o ℓ e) where
  open SymmetricMonoidalCategory C using (braidedMonoidalCategory)

  idF-StrongSymmetricMonoidal : Strong.SymmetricMonoidalFunctor C C
  idF-StrongSymmetricMonoidal = record
    { isBraidedMonoidal = idF-IsStrongBraidedMonoidal braidedMonoidalCategory }

  idF-SymmetricMonoidal : Lax.SymmetricMonoidalFunctor C C
  idF-SymmetricMonoidal = record
    { isBraidedMonoidal = idF-IsBraidedMonoidal braidedMonoidalCategory }

-- Functor composition preserves symmetric monoidality

module _ {A : SymmetricMonoidalCategory o ℓ e}
         {B : SymmetricMonoidalCategory o′ ℓ′ e′}
         {C : SymmetricMonoidalCategory o″ ℓ″ e″} where

  ∘-SymmetricMonoidal : Lax.SymmetricMonoidalFunctor B C →
                        Lax.SymmetricMonoidalFunctor A B →
                        Lax.SymmetricMonoidalFunctor A C
  ∘-SymmetricMonoidal G F = record
    { isBraidedMonoidal =
      ∘-IsBraidedMonoidal (isBraidedMonoidal G) (isBraidedMonoidal F)
    }
    where open Lax.SymmetricMonoidalFunctor hiding (F)

  ∘-StrongSymmetricMonoidal : Strong.SymmetricMonoidalFunctor B C →
                              Strong.SymmetricMonoidalFunctor A B →
                              Strong.SymmetricMonoidalFunctor A C
  ∘-StrongSymmetricMonoidal G F = record
    { isBraidedMonoidal =
      ∘-IsStrongBraidedMonoidal (isBraidedMonoidal G) (isBraidedMonoidal F)
    }
    where open Strong.SymmetricMonoidalFunctor hiding (F)
