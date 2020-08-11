{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric
open import Data.Sum

module Categories.Category.Monoidal.CompactClosed {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Level

open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Category.Monoidal.Rigid

open Category C
open Commutation C

record CompactClosed : Set (levelOfTerm M) where
  field
    symmetric : Symmetric M
    rigid     : LeftRigid M ⊎ RightRigid M
