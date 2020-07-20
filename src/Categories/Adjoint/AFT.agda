{-# OPTIONS --without-K --safe #-}

-- Adjoint Functor Theorem
module Categories.Adjoint.AFT where

open import Level
open import Data.Product using (Σ)

open import Categories.Category
open import Categories.Category.Complete
open import Categories.Functor
open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Morphism.Universal

import Categories.Diagram.Limit as Lim
import Categories.Adjoint.AFT.SolutionSet as SS

private
  variable
    o ℓ e i : Level
    C D : Category o ℓ e

module _ (Com : Complete o ℓ e C) {R : Functor C D} where
  private
    module C = Category C
    module D = Category D
    module R = Functor R
    module Com {J} F = Lim.Limit (Com {J = J} F)

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

  module _ (Ss : SolutionSet i) where
    open SolutionSet Ss
