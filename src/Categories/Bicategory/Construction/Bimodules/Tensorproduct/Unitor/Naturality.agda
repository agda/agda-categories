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
open Bimodulehomomorphism using (α)

open import Categories.Diagram.Coequalizer (hom (C M₁) (C M₂)) using (Coequalizer; Coequalizer⇒Epi)
open Coequalizer using (arr) 

import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} as TensorproductOfBimodules
import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq} as TensorproductOfHomomorphisms
open TensorproductOfBimodules using (CoeqBimods) renaming (Tensorproduct to infixr 30 _⊗₀_)
open TensorproductOfHomomorphisms using () renaming (Tensorproduct to infixr 30 _⊗₁_)
import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Unitor
  {o} {ℓ} {e} {t} {𝒞} {localCoeq} {M₁} {M₂} as Unitor

module Left-Unitor-natural where
  open Bimodule B using (actionʳ)
  open Bimodule B' using () renaming (actionʳ to actionʳ')
  open Unitor.Left-Unitor using (λ⇒-⊗; triangle)

  abstract
    λ⇒-⊗-natural-∘arr : (λ⇒-⊗ {B'} ∘ᵥ α (id-bimodule-hom ⊗₁ f)) ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B)
                      ≈ (α f ∘ᵥ λ⇒-⊗ {B}) ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B)
    λ⇒-⊗-natural-∘arr = begin
      (λ⇒-⊗ {B'} ∘ᵥ α (id-bimodule-hom ⊗₁ f)) ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B) ≈⟨ assoc₂ ⟩
      λ⇒-⊗ {B'} ∘ᵥ α (id-bimodule-hom ⊗₁ f) ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B)   ≈⟨ refl⟩∘⟨ ⟺ αSq-⊗ ⟩
      λ⇒-⊗ {B'} ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B') ∘ᵥ T M₂ ▷ α f                  ≈⟨ sym-assoc₂ ⟩
      (λ⇒-⊗ {B'} ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B')) ∘ᵥ T M₂ ▷ α f                ≈⟨ triangle {B'} ⟩∘⟨refl ⟩
      actionʳ' ∘ᵥ T M₂ ▷ α f                                           ≈⟨ linearʳ f ⟩
      α f ∘ᵥ actionʳ                                                 ≈⟨ refl⟩∘⟨ ⟺ (triangle {B}) ⟩
      α f ∘ᵥ λ⇒-⊗ {B} ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B)                         ≈⟨ sym-assoc₂ ⟩
      (α f ∘ᵥ λ⇒-⊗ {B}) ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B)                       ∎
      where
        open hom.HomReasoning
        open Bimodulehomomorphism using (linearʳ)
        open TensorproductOfHomomorphisms id-bimodule-hom f using (αSq-⊗)

    λ⇒-⊗-natural : λ⇒-⊗ {B'} ∘ᵥ α (id-bimodule-hom ⊗₁ f) ≈ α f ∘ᵥ λ⇒-⊗ {B}
    λ⇒-⊗-natural = Coequalizer⇒Epi
                    (CoeqBimods Id-Bimod B)
                    (λ⇒-⊗ ∘ᵥ α (id-bimodule-hom ⊗₁ f))
                    (α f ∘ᵥ λ⇒-⊗)
                    λ⇒-⊗-natural-∘arr

  -- end abstract --

module Right-Unitor-natural where
  open Bimodule B using (actionˡ)
  open Bimodule B' using () renaming (actionˡ to actionˡ')
  open Unitor.Right-Unitor using (ρ⇒-⊗; triangle)

  abstract
    ρ⇒-⊗-natural-∘arr : (ρ⇒-⊗ {B'} ∘ᵥ α (f ⊗₁ id-bimodule-hom)) ∘ᵥ Coequalizer.arr (CoeqBimods B Id-Bimod)
                      ≈ (α f ∘ᵥ ρ⇒-⊗ {B}) ∘ᵥ Coequalizer.arr (CoeqBimods B Id-Bimod)
    ρ⇒-⊗-natural-∘arr = begin
      (ρ⇒-⊗ {B'} ∘ᵥ α (f ⊗₁ id-bimodule-hom)) ∘ᵥ Coequalizer.arr (CoeqBimods B Id-Bimod) ≈⟨ assoc₂ ⟩
      ρ⇒-⊗ {B'} ∘ᵥ α (f ⊗₁ id-bimodule-hom) ∘ᵥ Coequalizer.arr (CoeqBimods B Id-Bimod)   ≈⟨ refl⟩∘⟨ ⟺ αSq-⊗ ⟩
      ρ⇒-⊗ {B'} ∘ᵥ Coequalizer.arr (CoeqBimods B' Id-Bimod) ∘ᵥ α f ◁ T M₁                  ≈⟨ sym-assoc₂ ⟩
      (ρ⇒-⊗ {B'} ∘ᵥ Coequalizer.arr (CoeqBimods B' Id-Bimod)) ∘ᵥ α f ◁ T M₁                ≈⟨ triangle {B'} ⟩∘⟨refl ⟩
      actionˡ' ∘ᵥ α f ◁ T M₁                                           ≈⟨ linearˡ f ⟩
      α f ∘ᵥ actionˡ                                                 ≈⟨ refl⟩∘⟨ ⟺ (triangle {B}) ⟩
      α f ∘ᵥ ρ⇒-⊗ {B} ∘ᵥ Coequalizer.arr (CoeqBimods B Id-Bimod)                         ≈⟨ sym-assoc₂ ⟩
      (α f ∘ᵥ ρ⇒-⊗ {B}) ∘ᵥ Coequalizer.arr (CoeqBimods B Id-Bimod)                       ∎
      where
        open hom.HomReasoning
        open Bimodulehomomorphism using (linearˡ)
        open TensorproductOfHomomorphisms f id-bimodule-hom using (αSq-⊗)

    ρ⇒-⊗-natural : ρ⇒-⊗ {B'} ∘ᵥ α (f ⊗₁ id-bimodule-hom) ≈ α f ∘ᵥ ρ⇒-⊗ {B}
    ρ⇒-⊗-natural = Coequalizer⇒Epi
                    (CoeqBimods B Id-Bimod)
                    (ρ⇒-⊗ ∘ᵥ α (f ⊗₁ id-bimodule-hom))
                    (α f ∘ᵥ ρ⇒-⊗)
                    ρ⇒-⊗-natural-∘arr

  -- end abstract --
