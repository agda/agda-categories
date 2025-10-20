{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Functorial {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} where

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism

open Monad using (C)
open Bimodulehomomorphism using (α)

open import Categories.Diagram.Coequalizer using (Coequalizer; Coequalizer⇒Epi)
open Coequalizer using (arr)

import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} as TensorproductOfBimodules
import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq} as TensorproductOfHomomorphisms
open TensorproductOfBimodules using (CoeqBimods) renaming (Tensorproduct to infixr 30 _⊗₀_)
open TensorproductOfHomomorphisms using () renaming (Tensorproduct to infixr 30 _⊗₁_)

module Identity {M₁ M₂ M₃ : Monad 𝒞} (B₂ : Bimodule M₂ M₃) (B₁ : Bimodule M₁ M₂) where

  ⊗₁-resp-id₂-∘arr : α (id-bimodule-hom {B = B₂} ⊗₁ id-bimodule-hom {B = B₁}) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)
                 ≈ id₂ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)
  ⊗₁-resp-id₂-∘arr = begin
    α (id-bimodule-hom {B = B₂} ⊗₁ id-bimodule-hom {B = B₁}) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ≈⟨ ⟺ αSq-⊗ ⟩
    Coequalizer.arr (CoeqBimods B₂ B₁) ∘ᵥ (id₂ ⊚₁ id₂) ≈⟨ refl⟩∘⟨ ⊚.identity ⟩
    Coequalizer.arr (CoeqBimods B₂ B₁) ∘ᵥ id₂ ≈⟨ identity₂ʳ ⟩
    Coequalizer.arr (CoeqBimods B₂ B₁) ≈⟨ ⟺ identity₂ˡ ⟩
    id₂ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ∎
    where
      open hom.HomReasoning
      open TensorproductOfHomomorphisms {B₂ = B₂} {B₂} {B₁} {B₁} (id-bimodule-hom) (id-bimodule-hom) using (αSq-⊗)

  ⊗₁-resp-id₂ : α (id-bimodule-hom {B = B₂} ⊗₁ id-bimodule-hom {B = B₁}) ≈ id₂
  ⊗₁-resp-id₂ = Coequalizer⇒Epi (hom (C M₁) (C M₃)) (CoeqBimods B₂ B₁)
                             (α (id-bimodule-hom {B = B₂} ⊗₁ id-bimodule-hom  {B = B₁}))
                             (α (id-bimodule-hom {B = B₂ ⊗₀ B₁}))
                             ⊗₁-resp-id₂-∘arr

module Composition {M₁ M₂ M₃ : Monad 𝒞} {B₂ B'₂ B''₂ : Bimodule M₂ M₃} {B₁ B'₁ B''₁ : Bimodule M₁ M₂}
                            (h₂ : Bimodulehomomorphism B'₂ B''₂) (h₁ : Bimodulehomomorphism B'₁ B''₁)
                            (g₂ : Bimodulehomomorphism B₂ B'₂) (g₁ : Bimodulehomomorphism B₁ B'₁) where
    
  ⊗₁-distr-∘ᵥ-∘arr : α (bimodule-hom-∘ h₂ g₂ ⊗₁ bimodule-hom-∘ h₁ g₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)
                    ≈ (α (h₂ ⊗₁ h₁) ∘ᵥ α (g₂ ⊗₁ g₁)) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)
  ⊗₁-distr-∘ᵥ-∘arr = begin
    α (bimodule-hom-∘ h₂ g₂ ⊗₁ bimodule-hom-∘ h₁ g₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)                        ≈⟨ ⟺ (αSq-⊗ (bimodule-hom-∘ h₂ g₂) (bimodule-hom-∘ h₁ g₁)) ⟩
    Coequalizer.arr (CoeqBimods B''₂ B''₁)
    ∘ᵥ ((α h₂ ∘ᵥ α g₂) ⊚₁ ((α h₁ ∘ᵥ Bimodulehomomorphism.α g₁))) ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-⊚ ⟩
    Coequalizer.arr (CoeqBimods B''₂ B''₁) ∘ᵥ (α h₂ ⊚₁ α h₁)
    ∘ᵥ (α g₂ ⊚₁ α g₁)                                            ≈⟨ glue′ (αSq-⊗ h₂ h₁) (αSq-⊗ g₂ g₁) ⟩
    (α (h₂ ⊗₁ h₁) ∘ᵥ α (g₂ ⊗₁ g₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)                        ∎
    where
      open hom.HomReasoning
      open import Categories.Morphism.Reasoning.Core (hom (C M₁) (C M₃)) using (glue′) -- TODO
      open TensorproductOfHomomorphisms using (αSq-⊗)

  ⊗₁-distr-∘ᵥ : α (bimodule-hom-∘ h₂ g₂ ⊗₁ bimodule-hom-∘ h₁ g₁)
                ≈ α (h₂ ⊗₁ h₁) ∘ᵥ α (g₂ ⊗₁ g₁)
  ⊗₁-distr-∘ᵥ = Coequalizer⇒Epi (hom (C M₁) (C M₃)) (CoeqBimods B₂ B₁)
                                (α (bimodule-hom-∘ h₂ g₂ ⊗₁ bimodule-hom-∘ h₁ g₁))
                                (α (h₂ ⊗₁ h₁) ∘ᵥ α (g₂ ⊗₁ g₁))
                                ⊗₁-distr-∘ᵥ-∘arr

module ≈Preservation {M₁ M₂ M₃ : Monad 𝒞} {B₂ B'₂ : Bimodule M₂ M₃} {B₁ B'₁ : Bimodule M₁ M₂}
                            (h₂ h'₂ : Bimodulehomomorphism B₂ B'₂) (h₁ h'₁ : Bimodulehomomorphism B₁ B'₁)
                            (e₂ : α h₂ ≈ α h'₂) (e₁ : α h₁ ≈ α h'₁) where

  ⊗₁-resp-≈-∘arr : α (h₂ ⊗₁ h₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ≈ α (h'₂ ⊗₁ h'₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)
  ⊗₁-resp-≈-∘arr = begin
    α (h₂ ⊗₁ h₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ≈⟨ ⟺ (αSq-⊗ h₂ h₁) ⟩
    Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α h₂ ⊚₁ α h₁) ≈⟨ refl⟩∘⟨ e₂ ⟩⊚⟨ e₁ ⟩
    Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α h'₂ ⊚₁ α h'₁) ≈⟨ αSq-⊗ h'₂ h'₁ ⟩
    α (h'₂ ⊗₁ h'₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ∎
    where
      open hom.HomReasoning
      open TensorproductOfHomomorphisms using (αSq-⊗)

  ⊗₁-resp-≈ : α (h₂ ⊗₁ h₁) ≈ α (h'₂ ⊗₁ h'₁)
  ⊗₁-resp-≈ = Coequalizer⇒Epi (hom (C M₁) (C M₃)) ((CoeqBimods B₂ B₁))
                              (α (h₂ ⊗₁ h₁)) (α (h'₂ ⊗₁ h'₁)) (⊗₁-resp-≈-∘arr)
