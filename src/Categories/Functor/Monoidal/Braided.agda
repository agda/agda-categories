{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal.Bundle
  using (BraidedMonoidalCategory)

module Categories.Functor.Monoidal.Braided {o o′ ℓ ℓ′ e e′}
  (C : BraidedMonoidalCategory o ℓ e) (D : BraidedMonoidalCategory o′ ℓ′ e′)
  where

open import Level
open import Data.Product using (_,_)

open import Categories.Category using (module Commutation)
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism)

open NaturalIsomorphism

private
  module C = BraidedMonoidalCategory C
  module D = BraidedMonoidalCategory D

module Lax where

  -- Lax braided monoidal functors.

  record IsBraidedMonoidalFunctor (F : Functor C.U D.U)
         : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
    open Functor F

    field
      isMonoidal : IsMonoidalFunctor C.monoidalCategory D.monoidalCategory F

    open IsMonoidalFunctor isMonoidal public
    open D
    open Commutation D.U

    -- coherence condition

    field
      braiding-compat : ∀ {X Y} →
                        [ F₀ X ⊗₀ F₀ Y                  ⇒ F₀ (Y C.⊗₀ X) ]⟨
                          ⊗-homo.η (X , Y)              ⇒⟨ F₀ (X C.⊗₀ Y) ⟩
                          F₁ (C.braiding.⇒.η (X , Y))
                        ≈ D.braiding.⇒.η (F₀ X , F₀ Y)  ⇒⟨ F₀ Y ⊗₀ F₀ X ⟩
                          ⊗-homo.η (Y , X)
                        ⟩

  record BraidedMonoidalFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      F                 : Functor C.U D.U
      isBraidedMonoidal : IsBraidedMonoidalFunctor F

    open Functor F public
    open IsBraidedMonoidalFunctor isBraidedMonoidal public

    monoidalFunctor : MonoidalFunctor C.monoidalCategory D.monoidalCategory
    monoidalFunctor = record { isMonoidal = isMonoidal }

module Strong where

  -- Strong braided monoidal functors.

  record IsBraidedMonoidalFunctor (F : Functor C.U D.U)
         : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
    open Functor F

    field
      isStrongMonoidal : IsStrongMonoidalFunctor C.monoidalCategory
                                                 D.monoidalCategory F

    open IsStrongMonoidalFunctor isStrongMonoidal public
    open D
    open Commutation D.U

    -- coherence condition

    field
      braiding-compat : ∀ {X Y} →
                        [ F₀ X ⊗₀ F₀ Y                  ⇒ F₀ (Y C.⊗₀ X) ]⟨
                          ⊗-homo.⇒.η (X , Y)            ⇒⟨ F₀ (X C.⊗₀ Y) ⟩
                          F₁ (C.braiding.⇒.η (X , Y))
                        ≈ D.braiding.⇒.η (F₀ X , F₀ Y)  ⇒⟨ F₀ Y ⊗₀ F₀ X ⟩
                          ⊗-homo.⇒.η (Y , X)
                        ⟩

    isLaxBraidedMonoidal : Lax.IsBraidedMonoidalFunctor F
    isLaxBraidedMonoidal = record
      { isMonoidal      = isMonoidal
      ; braiding-compat = braiding-compat
      }

  record BraidedMonoidalFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      F                 : Functor C.U D.U
      isBraidedMonoidal : IsBraidedMonoidalFunctor F

    open Functor F public
    open IsBraidedMonoidalFunctor isBraidedMonoidal public

    monoidalFunctor : StrongMonoidalFunctor C.monoidalCategory
                                            D.monoidalCategory
    monoidalFunctor = record { isStrongMonoidal = isStrongMonoidal }

    laxBraidedMonoidalFunctor : Lax.BraidedMonoidalFunctor
    laxBraidedMonoidalFunctor = record { isBraidedMonoidal = isLaxBraidedMonoidal }
