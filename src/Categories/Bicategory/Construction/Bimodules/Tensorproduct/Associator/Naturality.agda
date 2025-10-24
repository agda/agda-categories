{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism


-- We will define the associator in the bicategory of monads and bimodules. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator.Naturality
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ M₄ : Monad 𝒞}
  {B₃ B'₃ : Bimodule M₃ M₄} {B₂ B'₂ : Bimodule M₂ M₃} {B₁ B'₁ : Bimodule M₁ M₂}
  (f₃ : Bimodulehomomorphism B₃ B'₃) (f₂ : Bimodulehomomorphism B₂ B'₂) (f₁ : Bimodulehomomorphism B₁ B'₁) where

import Categories.Bicategory.LocalCoequalizers
open ComposeWithLocalCoequalizer 𝒞 localCoeq

import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} as TensorproductOfBimodules
import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq} as TensorproductOfHomomorphisms
open TensorproductOfBimodules using () renaming (Tensorproduct to infixr 30 _⊗₀_)
open TensorproductOfHomomorphisms using () renaming (Tensorproduct to infixr 30 _⊗₁_)

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands
import Categories.Diagram.Coequalizer
open import Categories.Category using (module Definitions)
import Categories.Morphism.Reasoning

-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    open Categories.Diagram.Coequalizer (hom X Y) public
    open Coequalizer using (arr) public

open HomCat

open TensorproductOfBimodules using (CoeqBimods)

open Monad using (C)
open Bimodule using (F)
open Bimodulehomomorphism using (α)

open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator
  {o} {ℓ} {e} {t} {𝒞} {localCoeq} {M₁} {M₂} {M₃} {M₄}
  using (α⇒-⊗; hexagon-sq)
  
abstract
  α⇒-⊗-natural-∘arr² : ((α⇒-⊗ {B'₃} {B'₂} {B'₁}
                          ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                          ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                          ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁
                        ≈ ((α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
                            ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁})
                            ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                            ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁
  α⇒-⊗-natural-∘arr² = begin

    ((α⇒-⊗ {B'₃} {B'₂} {B'₁}
    ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
    ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ≈⟨ assoc₂ ⟩

    (α⇒-⊗ {B'₃} {B'₂} {B'₁}
    ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
    ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ≈⟨ ⟺ associator-∘'⇒associator-⊗' ⟩

    (arr (CoeqBimods B'₃ (B'₂ ⊗₀ B'₁))
    ∘ᵥ F B'₃ ▷ arr (CoeqBimods B'₂ B'₁))
    ∘ᵥ α⇒
    ∘ᵥ (α f₃ ⊚₁ α f₂) ⊚₁ α f₁ ≈⟨ refl⟩∘⟨ α⇒-⊚ ⟩

    (arr (CoeqBimods B'₃ (B'₂ ⊗₀ B'₁))
    ∘ᵥ F B'₃ ▷ arr (CoeqBimods B'₂ B'₁))
    ∘ᵥ α f₃ ⊚₁ (α f₂ ⊚₁ α f₁)
    ∘ᵥ α⇒ ≈⟨ associator-∘⇒associator-⊗ ⟩

    (α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁})
    ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ≈⟨ ⟺ assoc₂ ⟩

    ((α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁})
    ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ∎

    where
      open hom.HomReasoning
      open Definitions (hom (C M₁) (C M₄)) using (CommutativeSquare)
      open TensorproductOfHomomorphisms using (αSq-⊗)
      open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (glue; glue′)

      abstract
        associator-∘'⇒associator-⊗' : CommutativeSquare
                                        (α⇒ {f = F B'₃} {F B'₂} {F B'₁} ∘ᵥ (α f₃ ⊚₁ α f₂) ⊚₁ α f₁)
                                        (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
                                        (arr (CoeqBimods B'₃ (B'₂ ⊗₀ B'₁)) ∘ᵥ F B'₃ ▷ arr (CoeqBimods B'₂ B'₁))
                                        (α⇒-⊗ {B₃ = B'₃} {B'₂} {B'₁} ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
        associator-∘'⇒associator-⊗' = glue′
                                        (hexagon-sq {B₃ = B'₃} {B'₂} {B'₁})
                                        (glue (αSq-⊗ (f₃ ⊗₁ f₂) f₁) (⊚-resp-sqˡ-degen (αSq-⊗ f₃ f₂)))

        associator-∘⇒associator-⊗ : CommutativeSquare
                                      (α f₃ ⊚₁ α f₂ ⊚₁ α f₁ ∘ᵥ α⇒ {f = F B₃} {F B₂} {F B₁})
                                      (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
                                      (arr (CoeqBimods B'₃ (B'₂ ⊗₀ B'₁)) ∘ᵥ F B'₃ ▷ arr (CoeqBimods B'₂ B'₁))
                                      (α (f₃ ⊗₁ f₂ ⊗₁ f₁) ∘ᵥ α⇒-⊗ {B₃ = B₃} {B₂} {B₁})
        associator-∘⇒associator-⊗ = glue′
                                      (glue (αSq-⊗ f₃ (f₂ ⊗₁ f₁)) (⊚-resp-sqʳ-degen (αSq-⊗ f₂ f₁)))
                                      (hexagon-sq {B₃ = B₃} {B₂} {B₁})


abstract
  α⇒-⊗-natural-∘arr : (α⇒-⊗ {B'₃} {B'₂} {B'₁}
                     ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                     ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                     ≈ (α (f₃ ⊗₁ (f₂ ⊗₁ f₁)) ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁})
                        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
  α⇒-⊗-natural-∘arr = Coequalizer⇒Epi
                      ((CoeqBimods B₃ B₂) coeq-◁ F B₁)
                      ((α⇒-⊗ {B'₃} {B'₂} {B'₁}
                        ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                      ((α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
                        ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁})
                        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                      α⇒-⊗-natural-∘arr²

abstract
  α⇒-⊗-natural : α⇒-⊗ {B'₃} {B'₂} {B'₁}
                ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁)
                ≈ α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
                  ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁}
  α⇒-⊗-natural = Coequalizer⇒Epi
                      (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                      (α⇒-⊗ ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                      (α (f₃ ⊗₁ f₂ ⊗₁ f₁) ∘ᵥ α⇒-⊗)
                      α⇒-⊗-natural-∘arr
-- end abstract --
