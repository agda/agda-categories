{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- Reasoning facilities about morphism equivalences (not necessarily 'squares')

module Categories.Morphism.Reasoning {o ℓ e} (C : Category o ℓ e) where

-- some items are defined in sub-modules
open import Categories.Morphism.Reasoning.Core C public
open import Categories.Morphism.Reasoning.Iso C public

open Category C
open Definitions C
open HomReasoning

-- create a commutative square from an equivalence
toSquare : ∀ {A B} {f g : A ⇒ B} → f ≈ g → CommutativeSquare f id id g
toSquare {_} {_} {f} {g} f≈g = begin
      id ∘ f   ≈⟨ identityˡ ⟩
      f        ≈⟨ f≈g ⟩
      g        ≈˘⟨ identityʳ ⟩
      g ∘ id   ∎
