{-# OPTIONS --without-K --safe #-}

-- Adjoint Functor Theorem
module Categories.Adjoint.AFT where

open import Level
open import Data.Product using (Σ)

open import Categories.Category
open import Categories.Category.Complete
open import Categories.Category.Complete.Properties
open import Categories.Category.Construction.Comma
open import Categories.Functor
open import Categories.Functor.Continuous
open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Morphism.Universal

import Categories.Diagram.Limit as Lim
import Categories.Adjoint.AFT.SolutionSet as SS

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

module _ {R : Functor C D} where
  private
    module C = Category C
    module D = Category D
    module R = Functor R

  open SS R

  module _ {L : Functor D C} (L⊣R : L ⊣ R) where
    private
      module L = Functor L
      open Adjoint L⊣R

    L⊣R⇒solutionSet′ : SolutionSet′
    L⊣R⇒solutionSet′ = record
      { S₀      = λ {_ X} _ → L.₀ X
      ; S₁      = Radjunct
      ; ϕ       = λ _ → unit.η _
      ; commute = λ _ → LRadjunct≈id
      }

  module _ (Com : Complete o ℓ e C) (Rcon : Continuous o ℓ e R) (s : SolutionSet′) where
    open SolutionSet′ s

    solutionSet′⇒universalMorphism : ∀ X → UniversalMorphism X R
    solutionSet′⇒universalMorphism X = record
      { initial = SolutionSet⇒Initial {o′ = 0ℓ} {0ℓ} {0ℓ} {C = X ↙ R} {!!} {!!}
      }

    solutionSet⇒adjoint : Σ (Functor D C) (λ L → L ⊣ R)
    solutionSet⇒adjoint = universalMophisms⇒adjoint solutionSet′⇒universalMorphism
