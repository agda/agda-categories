{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism


-- We will prove that the associator and unitor in the bicategory of monads and bimodules --
-- satisfies the triangle law. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Coherence.Triangle
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ : Monad 𝒞}
  {B₂ : Bimodule M₂ M₃} {B₁ : Bimodule M₁ M₂} where

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands

import Categories.Bicategory.LocalCoequalizers
open ComposeWithLocalCoequalizer 𝒞 localCoeq

open Monad using (C; T)
open Bimodule using (F; actionˡ; actionʳ)
open Bimodulehomomorphism using (α)

Id-Bimod : {M : Monad 𝒞} → Bimodule M M
Id-Bimod {M} = id-bimodule M

open import Categories.Category using (module Definitions)
import Categories.Diagram.Coequalizer
import Categories.Morphism
import Categories.Morphism.Reasoning
import Categories.Morphism.Reasoning.Iso

-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    open Categories.Morphism (hom X Y) public using (_≅_)
    open Categories.Diagram.Coequalizer (hom X Y) public
    open Coequalizer using (arr; equality) public
    open Categories.Morphism.Reasoning.Iso (hom X Y) public

open HomCat

open import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq}
  using (CoeqBimods) renaming (Tensorproduct to infixr 30 _⊗₀_)
open import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq}
  using (αSq-⊗) renaming (Tensorproduct to infixr 30 _⊗₁_)
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator {𝒞 = 𝒞} {localCoeq}
  using (associator-⊗-from; hexagon; hexagon-sq)
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Unitor {𝒞 = 𝒞} {localCoeq} using (module Left-Unitor; module Right-Unitor)
open Left-Unitor using (unitorˡ-⊗-from) renaming (triangle to unitorˡ-triangle)
open Right-Unitor using (unitorʳ-⊗-from) renaming (triangle to unitorʳ-triangle)

abstract
  triangle-⊗-∘arr² :
    ((α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₂} {Id-Bimod} {B₁}))
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
    ≈
    (α (unitorʳ-⊗-from {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁

  triangle-⊗-∘arr² = begin

    ((α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₂} {Id-Bimod} {B₁}))
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
                                                              ≈⟨ assoc₂ ⟩

    (α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₂} {Id-Bimod} {B₁}))
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁)
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
                                                              ≈⟨ extendˡ (⟺ (hexagon-sq {B₃ = B₂} {Id-Bimod} {B₁})) ⟩

    (α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
    ∘ᵥ (arr (CoeqBimods B₂ (Id-Bimod ⊗₀ B₁))
    ∘ᵥ F B₂ ▷ arr (CoeqBimods Id-Bimod B₁)))
    ∘ᵥ α⇒ {f = F B₂} {T M₂} {F B₁}
                                                              ≈⟨ ⟺ (pullˡ associator-∘⇒unitor-⊗) ⟩

    (arr (CoeqBimods B₂ B₁)
    ∘ᵥ actionˡ B₂ ◁ F B₁)
    ∘ᵥ α⇐ {f = F B₂} {T M₂} {F B₁}
    ∘ᵥ α⇒ {f = F B₂} {T M₂} {F B₁}
                                                              ≈⟨ elimʳ associator.isoˡ ⟩

    arr (CoeqBimods B₂ B₁)
    ∘ᵥ actionˡ B₂ ◁ F B₁
                                                              ≈⟨ id⇒unitor-⊗ ⟩

    α (unitorʳ-⊗-from {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁)
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
                                                              ≈⟨ ⟺ assoc₂ ⟩

    (α (unitorʳ-⊗-from {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁                    ∎

    where
      open hom.HomReasoning
      open Definitions (hom (C M₁) (C M₃)) using (CommutativeSquare)
      open Categories.Morphism.Reasoning (hom (C M₁) (C M₃)) using (pullˡ; pullʳ; elimʳ; glue◽◃; glue▹◽; extendˡ)

      associator-∘⇒unitor-⊗ : CommutativeSquare
                                (α⇐ {f = F B₂} {T M₂} {F B₁})
                                (arr (CoeqBimods B₂ (Id-Bimod ⊗₀ B₁)) ∘ᵥ F B₂ ▷ arr (CoeqBimods Id-Bimod B₁))
                                (arr (CoeqBimods B₂ B₁) ∘ᵥ actionˡ B₂ ◁ F B₁)
                                (α (id-bimodule-hom ⊗₁ unitorˡ-⊗-from {B = B₁}))

      associator-∘⇒unitor-⊗ = begin

        (arr (CoeqBimods B₂ B₁)
        ∘ᵥ actionˡ B₂ ◁ F B₁)
        ∘ᵥ α⇐ {f = F B₂} {T M₂} {F B₁}          ≈⟨ assoc₂ ⟩

        arr (CoeqBimods B₂ B₁)
        ∘ᵥ actionˡ B₂ ◁ F B₁
        ∘ᵥ α⇐ {f = F B₂} {T M₂} {F B₁}          ≈⟨ ⟺ (equality (CoeqBimods B₂ B₁)) ⟩

        arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₂ ▷ actionʳ B₁                    ≈⟨ ⟺ (glue▹◽ (▷-resp-tri unitorˡ-triangle) (⟺ (αSq-⊗ id-bimodule-hom unitorˡ-⊗-from))) ⟩

        α (id-bimodule-hom ⊗₁ unitorˡ-⊗-from)
        ∘ᵥ arr (CoeqBimods B₂ (Id-Bimod ⊗₀ B₁))
        ∘ᵥ F B₂ ▷ arr (CoeqBimods Id-Bimod B₁)  ∎

      id⇒unitor-⊗ :
        arr (CoeqBimods B₂ B₁)
        ∘ᵥ actionˡ B₂ ◁ F B₁
        ≈
        α (unitorʳ-⊗-from {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})
        ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁)
        ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
      id⇒unitor-⊗ = ⟺ (glue▹◽ (◁-resp-tri unitorʳ-triangle) (⟺ (αSq-⊗ unitorʳ-⊗-from id-bimodule-hom)))


  triangle-⊗-∘arr :
    (α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₂} {Id-Bimod} {B₁}))
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁)
    ≈
    α (unitorʳ-⊗-from {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁)
                    
  triangle-⊗-∘arr = Coequalizer⇒Epi
                      ((CoeqBimods B₂ Id-Bimod) coeq-◁ F B₁)
                      ((α (id-bimodule-hom ⊗₁ unitorˡ-⊗-from) ∘ᵥ α associator-⊗-from) ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
                      (α (unitorʳ-⊗-from ⊗₁ id-bimodule-hom) ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
                      triangle-⊗-∘arr²
  
  triangle-⊗ : α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁}) ∘ᵥ α (associator-⊗-from {B₃ = B₂} {Id-Bimod} {B₁})
             ≈ α (unitorʳ-⊗-from {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})

  triangle-⊗ = Coequalizer⇒Epi
                 (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁)
                 (α (id-bimodule-hom ⊗₁ unitorˡ-⊗-from) ∘ᵥ α associator-⊗-from)
                 (α (unitorʳ-⊗-from ⊗₁ id-bimodule-hom))
                 triangle-⊗-∘arr
