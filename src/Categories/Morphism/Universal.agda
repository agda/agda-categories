{-# OPTIONS --without-K --safe #-}

module Categories.Morphism.Universal where

open import Level
open import Categories.Category
open import Categories.Category.Construction.Comma
open import Categories.Functor
open import Categories.Object.Initial

record UniversalMorphism {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
                         (X : Category.Obj C) (F : Functor D C) : Set (e ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  X↙F : Category _ _ _
  X↙F = X ↙ F

  private
    module X↙F = Category X↙F
   
  field
    initial : Initial X↙F

  module initial = Initial initial
  open initial public
