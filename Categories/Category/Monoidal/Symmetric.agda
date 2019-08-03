{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal

module Categories.Category.Monoidal.Symmetric {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Level

open import Data.Product using (Σ; _,_)

open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation.NaturalIsomorphism

open import Categories.Morphism C
open import Categories.Category.Monoidal.Braided M
open Category C
open Commutation

private
  variable
    X Y Z : Obj

-- symmetric monoidal category
-- commutative braided monoidal category
record Symmetric : Set (levelOfTerm M) where
  field
    braided : Braided

  module braided = Braided braided
  open braided public

  private
    B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
    B {X} {Y} = braiding.⇒.η (X , Y)

  field
    commutative : B {X} {Y} ∘ B {Y} {X} ≈ id

  braided-iso : X ⊗₀ Y ≅ Y ⊗₀ X
  braided-iso = record
    { from = B
    ; to   = B
    ; iso  = record
      { isoˡ = commutative
      ; isoʳ = commutative
      }
    }
