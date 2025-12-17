{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism


-- We will show that the left- and right-unitor in the bicategory of monads and bimodules is natural. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Unitor.Naturality
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞}
  {M₁ M₂ : Monad 𝒞} {B B' : Bimodule M₁ M₂} (f : Bimodulehomomorphism B B') where

Id-Bimod : {M : Monad 𝒞} → Bimodule M M
Id-Bimod {M} = id-bimodule M

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞 hiding (triangle)
open Shorthands

open Monad using (C; T)
open Bimodule using (actionˡ; actionʳ)
open Bimodulehomomorphism using (α; linearˡ; linearʳ)

import Categories.Morphism.Reasoning
open import Categories.Diagram.Coequalizer (hom (C M₁) (C M₂)) using (Coequalizer; Coequalizer⇒Epi)
open Coequalizer using (arr)

open import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} as TensorproductOfBimodules
  using (CoeqBimods) renaming (Tensorproduct to infixr 30 _⊗₀_)
open import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq} as TensorproductOfHomomorphisms
  using () renaming (Tensorproduct to infixr 30 _⊗₁_)
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Unitor {𝒞 = 𝒞} {localCoeq} {M₁} {M₂}
  using (module Left-Unitor; module Right-Unitor)

module Left-Unitor-natural where
  open Left-Unitor using (λ⇒-⊗; triangle)

  abstract
    λ⇒-⊗-natural-∘arr : (λ⇒-⊗ {B'} ∘ᵥ α (id-bimodule-hom ⊗₁ f)) ∘ᵥ arr (CoeqBimods Id-Bimod B)
                      ≈ (α f ∘ᵥ λ⇒-⊗ {B}) ∘ᵥ arr (CoeqBimods Id-Bimod B)
    λ⇒-⊗-natural-∘arr = begin
      (λ⇒-⊗ {B'} ∘ᵥ α (id-bimodule-hom ⊗₁ f)) ∘ᵥ arr (CoeqBimods Id-Bimod B) ≈⟨ pullʳ (⟺ (αSq-⊗ id-bimodule-hom f)) ⟩
      λ⇒-⊗ {B'} ∘ᵥ arr (CoeqBimods Id-Bimod B') ∘ᵥ T M₂ ▷ α f                ≈⟨ pullˡ (triangle {B'}) ⟩
      actionʳ B' ∘ᵥ T M₂ ▷ α f                                               ≈⟨ linearʳ f ⟩
      α f ∘ᵥ actionʳ B                                                       ≈⟨ pushʳ (⟺ (triangle {B})) ⟩
      (α f ∘ᵥ λ⇒-⊗ {B}) ∘ᵥ arr (CoeqBimods Id-Bimod B)                       ∎
      where
        open hom.HomReasoning
        open Categories.Morphism.Reasoning (hom (C M₁) (C M₂)) using (pullˡ; pullʳ; pushʳ)
        open TensorproductOfHomomorphisms using (αSq-⊗)

    λ⇒-⊗-natural : λ⇒-⊗ {B'} ∘ᵥ α (id-bimodule-hom ⊗₁ f) ≈ α f ∘ᵥ λ⇒-⊗ {B}
    λ⇒-⊗-natural = Coequalizer⇒Epi
                    (CoeqBimods Id-Bimod B)
                    (λ⇒-⊗ ∘ᵥ α (id-bimodule-hom ⊗₁ f))
                    (α f ∘ᵥ λ⇒-⊗)
                    λ⇒-⊗-natural-∘arr
  -- end abstract --

module Right-Unitor-natural where
  open Right-Unitor using (ρ⇒-⊗; triangle)

  abstract
    ρ⇒-⊗-natural-∘arr : (ρ⇒-⊗ {B'} ∘ᵥ α (f ⊗₁ id-bimodule-hom)) ∘ᵥ arr (CoeqBimods B Id-Bimod)
                      ≈ (α f ∘ᵥ ρ⇒-⊗ {B}) ∘ᵥ arr (CoeqBimods B Id-Bimod)
    ρ⇒-⊗-natural-∘arr = begin
      (ρ⇒-⊗ {B'} ∘ᵥ α (f ⊗₁ id-bimodule-hom)) ∘ᵥ arr (CoeqBimods B Id-Bimod) ≈⟨ pullʳ (⟺ (αSq-⊗ f id-bimodule-hom)) ⟩
      ρ⇒-⊗ {B'} ∘ᵥ arr (CoeqBimods B' Id-Bimod) ∘ᵥ α f ◁ T M₁                ≈⟨ pullˡ (triangle {B'}) ⟩
      actionˡ B' ∘ᵥ α f ◁ T M₁                                               ≈⟨ linearˡ f ⟩
      α f ∘ᵥ actionˡ B                                                       ≈⟨ pushʳ (⟺ (triangle {B})) ⟩
      (α f ∘ᵥ ρ⇒-⊗ {B}) ∘ᵥ arr (CoeqBimods B Id-Bimod)                       ∎
      where
        open hom.HomReasoning
        open Categories.Morphism.Reasoning (hom (C M₁) (C M₂)) using (pullˡ; pullʳ; pushʳ)
        open TensorproductOfHomomorphisms using (αSq-⊗)

    ρ⇒-⊗-natural : ρ⇒-⊗ {B'} ∘ᵥ α (f ⊗₁ id-bimodule-hom) ≈ α f ∘ᵥ ρ⇒-⊗ {B}
    ρ⇒-⊗-natural = Coequalizer⇒Epi
                    (CoeqBimods B Id-Bimod)
                    (ρ⇒-⊗ ∘ᵥ α (f ⊗₁ id-bimodule-hom))
                    (α f ∘ᵥ ρ⇒-⊗)
                    ρ⇒-⊗-natural-∘arr
  -- end abstract --
