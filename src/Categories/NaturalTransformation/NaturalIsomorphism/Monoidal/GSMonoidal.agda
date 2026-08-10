{-# OPTIONS --without-K --safe #-}

-- Isomorphism of gs-monoidal functors.
--
-- A gs-monoidal natural transformation is a monoidal one and nothing more:
-- neither comonoid map is natural, so there is no further square to respect,
-- and `copy` and `discard` are conditions on a functor rather than structure
-- an isomorphism could fail to preserve.  The relation is therefore the
-- symmetric monoidal one on the underlying functors.
--
-- Naming it at this rung is what the module is for.  Without it every client
-- reaches past the gs-monoidal layer and states its theorems about symmetric
-- monoidal functors, each with its own local renaming of
-- `symmetricMonoidalFunctor`, as `Categories.Category.Instance.GSMonoidals`
-- did twice before this module existed.

module Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.GSMonoidal
  where

open import Level using (Level; _⊔_)

open import Function.Base using (_on_)
open import Relation.Binary using (Rel; IsEquivalence)
import Relation.Binary.Construct.On as On

open import Categories.Category.Monoidal.GSMonoidal.Bundle using (GSMonoidalCategory)

import Categories.Functor.Monoidal.GSMonoidal as GSMF
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric as SMNI

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

module Lax {C : GSMonoidalCategory o ℓ e} {D : GSMonoidalCategory o′ ℓ′ e′} where

  open GSMF.Lax using (GSMonoidalFunctor)
  open GSMonoidalFunctor using (symmetricMonoidalFunctor)

  infix 4 _≃_

  _≃_ : Rel (GSMonoidalFunctor C D) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′)
  _≃_ = SMNI.Lax._≃_ on symmetricMonoidalFunctor

  -- Being a relation taken along a function, this comes from the symmetric
  -- monoidal one by Relation.Binary.Construct.On.

  isEquivalence : IsEquivalence _≃_
  isEquivalence =
    On.isEquivalence symmetricMonoidalFunctor SMNI.Lax.isEquivalence

module Strong {C : GSMonoidalCategory o ℓ e} {D : GSMonoidalCategory o′ ℓ′ e′}
  where

  open GSMF.Strong using (GSMonoidalFunctor)
  open GSMonoidalFunctor using (symmetricMonoidalFunctor)

  infix 4 _≃_

  _≃_ : Rel (GSMonoidalFunctor C D) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′)
  _≃_ = SMNI.Strong._≃_ on symmetricMonoidalFunctor

  isEquivalence : IsEquivalence _≃_
  isEquivalence =
    On.isEquivalence symmetricMonoidalFunctor SMNI.Strong.isEquivalence
