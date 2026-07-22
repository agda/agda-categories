{-# OPTIONS --without-K --safe --lossy-unification #-}
-- --lossy-unification makes this typecheck in ~4s instead of ~23s

-- In a symmetric rigid monoidal category, dualization is a strong symmetric
-- monoidal equivalence with the opposite category.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Category.Monoidal.Rigid.Functor.Symmetric
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C) (S : Symmetric M) where

open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Rigid using (LeftRigid; RightRigid)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
import Categories.Functor.Monoidal.Symmetric as SymmetricFunctor
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; _≃_; niHelper)
open import Data.Sum

open Category C
import Categories.Category.Monoidal.Construction.Reverse as Reverse
import Categories.Category.Monoidal.Rigid.Functor as RigidFunctor
import Categories.Category.Monoidal.Rigid.Symmetry as RigidSymmetry
open import Categories.Morphism C using (_≅_)

module Symmetry = RigidSymmetry {C = C} M S

symmetricMonoidalCategory : SymmetricMonoidalCategory o ℓ e
symmetricMonoidalCategory = record { symmetric = S }

private
  C-op-reverse : SymmetricMonoidalCategory o ℓ e
  C-op-reverse = Reverse.Reverse-SymmetricMonoidalCategory
    (SymmetricMonoidalCategory.op symmetricMonoidalCategory)

  variable
    X : Obj

module DoubleDualˡ (L : LeftRigid M) where
  open LeftRigid L using (_⁻¹)
  open import Categories.Category.Monoidal.Rigid.Dual M L using (dualFunctor)
  open Symmetry.DoubleDualˡ L
    using (⁻¹⁻¹≅; double-dual-natural; dual-braiding-compat; j⇒; j⇐)
  module DualFunctor = RigidFunctor {C = C} M L

  dual-Reverse-StrongSymmetricMonoidalFunctor :
    SymmetricFunctor.Strong.SymmetricMonoidalFunctor
      symmetricMonoidalCategory C-op-reverse
  dual-Reverse-StrongSymmetricMonoidalFunctor = record
    { F = dualFunctor
    ; isBraidedMonoidal = record
      { isStrongMonoidal = DualFunctor.dual-IsStrongMonoidalFunctor
      ; braiding-compat = dual-braiding-compat
      }
    }

  dual-StrongSymmetricMonoidalFunctor :
    SymmetricFunctor.Strong.SymmetricMonoidalFunctor
      symmetricMonoidalCategory
      (SymmetricMonoidalCategory.op symmetricMonoidalCategory)
  dual-StrongSymmetricMonoidalFunctor =
    Reverse.unreverse-StrongSymmetricMonoidal
      dual-Reverse-StrongSymmetricMonoidalFunctor

  double-dual≃id : Functor.op dualFunctor ∘F dualFunctor ≃ idF
  double-dual≃id = niHelper record
    { η       = λ _ → j⇒
    ; η⁻¹     = λ _ → j⇐
    ; commute = double-dual-natural
    ; iso     = λ X → _≅_.iso (⁻¹⁻¹≅ {X = X})
    }

  dual-equivalence : StrongEquivalence C (Category.op C)
  dual-equivalence = record
    { F = dualFunctor
    ; G = Functor.op dualFunctor
    ; weak-inverse = record
      { F∘G≈id = NaturalIsomorphism.op′ double-dual≃id
      ; G∘F≈id = double-dual≃id
      }
    }

module DoubleDualʳ (R : RightRigid M) where
  dual-equivalence : StrongEquivalence C (Category.op C)
  dual-equivalence = DoubleDualˡ.dual-equivalence (Symmetry.right⇒left R)

  dual-StrongSymmetricMonoidalFunctor :
    SymmetricFunctor.Strong.SymmetricMonoidalFunctor
      symmetricMonoidalCategory
      (SymmetricMonoidalCategory.op symmetricMonoidalCategory)
  dual-StrongSymmetricMonoidalFunctor =
    DoubleDualˡ.dual-StrongSymmetricMonoidalFunctor (Symmetry.right⇒left R)

dual-equivalence : LeftRigid M ⊎ RightRigid M → StrongEquivalence C (Category.op C)
dual-equivalence = [ DoubleDualˡ.dual-equivalence , DoubleDualʳ.dual-equivalence ]′

dual-StrongSymmetricMonoidalFunctor : LeftRigid M ⊎ RightRigid M →
  SymmetricFunctor.Strong.SymmetricMonoidalFunctor
    symmetricMonoidalCategory
    (SymmetricMonoidalCategory.op symmetricMonoidalCategory)
dual-StrongSymmetricMonoidalFunctor =
  [ DoubleDualˡ.dual-StrongSymmetricMonoidalFunctor
  , DoubleDualʳ.dual-StrongSymmetricMonoidalFunctor
  ]′
