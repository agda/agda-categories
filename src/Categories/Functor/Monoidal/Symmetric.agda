{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal.Structure
  using (SymmetricMonoidalCategory)

module Categories.Functor.Monoidal.Symmetric {o o′ ℓ ℓ′ e e′}
  (C : SymmetricMonoidalCategory o ℓ e) (D : SymmetricMonoidalCategory o′ ℓ′ e′)
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
  module C = SymmetricMonoidalCategory C
  module D = SymmetricMonoidalCategory D

module Lax where

  -- Lax symmetric monoidal functors.

  record IsSymmetricMonoidalFunctor (F : Functor C.U D.U)
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

  record SymmetricMonoidalFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      F                   : Functor C.U D.U
      isSymmetricMonoidal : IsSymmetricMonoidalFunctor F

    open Functor F public
    open IsSymmetricMonoidalFunctor isSymmetricMonoidal public

    monoidalFunctor : MonoidalFunctor C.monoidalCategory D.monoidalCategory
    monoidalFunctor = record { F = F ; isMonoidal = isMonoidal }

module Strong where

  -- Strong symmetric monoidal functors.

  record IsSymmetricMonoidalFunctor (F : Functor C.U D.U)
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

    isLaxSymmetricMonoidal : Lax.IsSymmetricMonoidalFunctor F
    isLaxSymmetricMonoidal = record
      { isMonoidal      = isMonoidal
      ; braiding-compat = braiding-compat
      }

  record SymmetricMonoidalFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      F                   : Functor C.U D.U
      isSymmetricMonoidal : IsSymmetricMonoidalFunctor F

    open Functor F public
    open IsSymmetricMonoidalFunctor isSymmetricMonoidal public

    monoidalFunctor : StrongMonoidalFunctor C.monoidalCategory
                                            D.monoidalCategory
    monoidalFunctor = record { F = F ; isStrongMonoidal = isStrongMonoidal }
