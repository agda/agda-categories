{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal.Core using (Monoidal)

module Categories.Category.Monoidal.Braided {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Level

open import Data.Product using (Σ; _,_)

open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation.NaturalIsomorphism

open Category C
open Commutation C

private
  variable
    X Y Z : Obj

-- braided monoidal category
-- it has a braiding natural isomorphism has two hexagon identities.
-- these two identities are directly expressed in the morphism level.
record Braided : Set (levelOfTerm M) where
  open Monoidal M public

  field
    braiding : NaturalIsomorphism ⊗ (flip-bifunctor ⊗)

  module braiding = NaturalIsomorphism braiding

  private
    B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
    B {X} {Y} = braiding.⇒.η (X , Y)

  field
    hexagon₁ : [ (X ⊗₀ Y) ⊗₀ Z ⇒ Y ⊗₀ Z ⊗₀ X ]⟨
                 B  ⊗₁ id                    ⇒⟨ (Y ⊗₀ X) ⊗₀ Z ⟩
                 associator.from             ⇒⟨ Y ⊗₀ X ⊗₀ Z ⟩
                 id ⊗₁ B
               ≈ associator.from             ⇒⟨ X ⊗₀ Y ⊗₀ Z ⟩
                 B                           ⇒⟨ (Y ⊗₀ Z) ⊗₀ X ⟩
                 associator.from
               ⟩
    hexagon₂ : [ X ⊗₀ Y ⊗₀ Z ⇒ (Z ⊗₀ X) ⊗₀ Y ]⟨
                 id ⊗₁ B                     ⇒⟨ X ⊗₀ Z ⊗₀ Y ⟩
                 (associator.to              ⇒⟨ (X ⊗₀ Z) ⊗₀ Y ⟩
                 B ⊗₁ id)
               ≈ associator.to               ⇒⟨ (X ⊗₀ Y) ⊗₀ Z ⟩
                 (B                          ⇒⟨ Z ⊗₀ X ⊗₀ Y ⟩
                 associator.to)
               ⟩
