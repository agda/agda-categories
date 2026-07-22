{-# OPTIONS --without-K --safe --lossy-unification #-}
-- --lossy-unification makes this typecheck in ~3s instead of ~25s

-- Compact closure transfers to the opposite monoidal category, and dualization
-- gives a strong symmetric monoidal equivalence with the opposite category.

open import Categories.Category.Core using (Category)
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.CompactClosed using (CompactClosed)
open import Categories.Category.Monoidal.Core using (Monoidal)
import Categories.Category.Monoidal.Rigid.Functor.Symmetric as RigidFunctor
import Categories.Functor.Monoidal.Symmetric as SymmetricFunctor

module Categories.Category.Monoidal.CompactClosed.Properties
    {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (K : CompactClosed M) where

open import Data.Sum using (inj₁)

open import Categories.Category.Monoidal.Properties M using (monoidal-Op)
open import Categories.Category.Monoidal.Rigid.Properties M using (rigidʳ-Op)
open import Categories.Category.Monoidal.Symmetric.Properties using (symmetric-Op)
import Categories.Category.Monoidal.CompactClosed monoidal-Op as OpCompactClosed

open CompactClosed K
open import Categories.Category.Monoidal.Rigid.Dual M leftRigid using (dualFunctor)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)

symmetricMonoidalCategory : SymmetricMonoidalCategory o ℓ e
symmetricMonoidalCategory = record { symmetric = symmetric }

compactClosed-Op : OpCompactClosed.CompactClosed
compactClosed-Op = record
  { symmetric = symmetric-Op symmetric
  ; rigid     = inj₁ (rigidʳ-Op rightRigid)
  }

dual²≃id : Functor.op dualFunctor ∘F dualFunctor ≃ idF
dual²≃id = RigidFunctor.DoubleDualˡ.double-dual≃id {C = C} M symmetric leftRigid

dual-equivalence : StrongEquivalence C (Category.op C)
dual-equivalence = RigidFunctor.dual-equivalence {C = C} M symmetric rigid

dual-StrongSymmetricMonoidalFunctor :
  SymmetricFunctor.Strong.SymmetricMonoidalFunctor
    symmetricMonoidalCategory
    (SymmetricMonoidalCategory.op symmetricMonoidalCategory)
dual-StrongSymmetricMonoidalFunctor =
  RigidFunctor.dual-StrongSymmetricMonoidalFunctor {C = C} M symmetric rigid
