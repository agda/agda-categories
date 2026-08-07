{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal.GSMonoidal.Bundle using (GSMonoidalCategory)

-- GS-monoidal functors: symmetric monoidal functors that also carry the
-- comonoid structure of the domain to the comonoid structure of the codomain.
-- Since neither comonoid map is natural, preservation is an extra condition
-- rather than a consequence, and it takes two laws, one per map.

module Categories.Functor.Monoidal.GSMonoidal {o o′ ℓ ℓ′ e e′}
  (C : GSMonoidalCategory o ℓ e) (D : GSMonoidalCategory o′ ℓ′ e′) where

open import Level
open import Data.Product using (_,_)

open import Categories.Category using (module Commutation)
open import Categories.Functor using (Functor)

private
  module C = GSMonoidalCategory C
  module D = GSMonoidalCategory D

import Categories.Functor.Monoidal.Braided
  C.braidedMonoidalCategory D.braidedMonoidalCategory as Braided
import Categories.Functor.Monoidal.Symmetric
  C.symmetricMonoidalCategory D.symmetricMonoidalCategory as Symmetric

module Lax where
  open Braided.Lax using (IsBraidedMonoidalFunctor)
  open Symmetric.Lax using (SymmetricMonoidalFunctor)

  -- Lax gs-monoidal functors.

  record IsGSMonoidalFunctor (F : Functor C.U D.U) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
    open Functor F

    field
      isBraidedMonoidal : IsBraidedMonoidalFunctor F

    open IsBraidedMonoidalFunctor isBraidedMonoidal public
    open D
    open Commutation D.U

    -- coherence conditions

    field
      copy    : ∀ {X} →
                [ F₀ X ⇒ F₀ (X C.⊗₀ X) ]⟨
                  Δ                    ⇒⟨ F₀ X ⊗₀ F₀ X ⟩
                  ⊗-homo.η (X , X)
                ≈ F₁ C.Δ
                ⟩
      discard : ∀ {X} →
                [ F₀ X ⇒ F₀ C.unit ]⟨
                  δ                 ⇒⟨ unit ⟩
                  ε
                ≈ F₁ C.δ
                ⟩

  record GSMonoidalFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      F            : Functor C.U D.U
      isGSMonoidal : IsGSMonoidalFunctor F

    open Functor F public
    open IsGSMonoidalFunctor isGSMonoidal public

    symmetricMonoidalFunctor : SymmetricMonoidalFunctor
    symmetricMonoidalFunctor = record { isBraidedMonoidal = isBraidedMonoidal }

module Strong where
  open Braided.Strong using (IsBraidedMonoidalFunctor)
  open Symmetric.Strong using (SymmetricMonoidalFunctor)

  -- Strong gs-monoidal functors.

  record IsGSMonoidalFunctor (F : Functor C.U D.U) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
    open Functor F

    field
      isBraidedMonoidal : IsBraidedMonoidalFunctor F

    open IsBraidedMonoidalFunctor isBraidedMonoidal public
    open D
    open Commutation D.U

    -- coherence conditions

    field
      copy    : ∀ {X} →
                [ F₀ X ⇒ F₀ (X C.⊗₀ X) ]⟨
                  Δ                    ⇒⟨ F₀ X ⊗₀ F₀ X ⟩
                  ⊗-homo.⇒.η (X , X)
                ≈ F₁ C.Δ
                ⟩
      discard : ∀ {X} →
                [ F₀ X ⇒ F₀ C.unit ]⟨
                  δ                 ⇒⟨ unit ⟩
                  ε.from
                ≈ F₁ C.δ
                ⟩

    isLaxGSMonoidal : Lax.IsGSMonoidalFunctor F
    isLaxGSMonoidal = record
      { isBraidedMonoidal = isLaxBraidedMonoidal
      ; copy              = copy
      ; discard           = discard
      }

  record GSMonoidalFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      F            : Functor C.U D.U
      isGSMonoidal : IsGSMonoidalFunctor F

    open Functor F public
    open IsGSMonoidalFunctor isGSMonoidal public

    symmetricMonoidalFunctor : SymmetricMonoidalFunctor
    symmetricMonoidalFunctor = record { isBraidedMonoidal = isBraidedMonoidal }

    laxGSMonoidalFunctor : Lax.GSMonoidalFunctor
    laxGSMonoidalFunctor = record { isGSMonoidal = isLaxGSMonoidal }
