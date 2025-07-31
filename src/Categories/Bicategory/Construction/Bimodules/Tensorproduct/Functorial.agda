{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Functorial {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} where

open import Categories.Bicategory.Monad
open import Level
open import Categories.Bicategory.Monad.Bimodule {o} {ℓ} {e} {t} {𝒞}
open import Categories.Bicategory.Monad.Bimodule.Homomorphism
open Bimodulehomomorphism
import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} as TensorproductOfBimodules
import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq} as TensorproductOfHomomorphisms

_⊗₀_ = TensorproductOfBimodules.B₂⊗B₁
_⊗₁_ = TensorproductOfHomomorphisms.h₂⊗h₁

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open import Categories.Diagram.Coequalizer

open TensorproductOfBimodules using (CoeqBimods)

module Identity {M₁ M₂ M₃ : Monad 𝒞} (B₂ : Bimodule M₂ M₃) (B₁ : Bimodule M₁ M₂) where
  open Monad M₁ using () renaming (C to C₁)
  open Monad M₃ using () renaming (C to C₃)

  ⊗₁-resp-id₂∘arr : α (id-bimodule-hom {B = B₂} ⊗₁ id-bimodule-hom {B = B₁}) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)
                 ≈ id₂ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)
  ⊗₁-resp-id₂∘arr = begin
    α (id-bimodule-hom {B = B₂} ⊗₁ id-bimodule-hom {B = B₁}) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ≈⟨ ⟺ αSq ⟩
    Coequalizer.arr (CoeqBimods B₂ B₁) ∘ᵥ (id₂ ⊚₁ id₂) ≈⟨ refl⟩∘⟨ ⊚.identity ⟩
    Coequalizer.arr (CoeqBimods B₂ B₁) ∘ᵥ id₂ ≈⟨ identity₂ʳ ⟩
    Coequalizer.arr (CoeqBimods B₂ B₁) ≈⟨ ⟺ identity₂ˡ ⟩
    id₂ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ∎
    where
      open hom.HomReasoning
      open TensorproductOfHomomorphisms {B₂ = B₂} {B₂} {B₁} {B₁} (id-bimodule-hom) (id-bimodule-hom) using (αSq)

  ⊗₁-resp-id₂ : α (id-bimodule-hom {B = B₂} ⊗₁ id-bimodule-hom {B = B₁}) ≈ id₂
  ⊗₁-resp-id₂ = Coequalizer⇒Epi (hom C₁ C₃) (CoeqBimods B₂ B₁)
                             (α (id-bimodule-hom {B = B₂} ⊗₁ id-bimodule-hom  {B = B₁}))
                             (α (id-bimodule-hom {B = B₂ ⊗₀ B₁}))
                             ⊗₁-resp-id₂∘arr

module Composition {M₁ M₂ M₃ : Monad 𝒞} {B₂ B'₂ B''₂ : Bimodule M₂ M₃} {B₁ B'₁ B''₁ : Bimodule M₁ M₂}
                            (h₂ : Bimodulehomomorphism B'₂ B''₂) (h₁ : Bimodulehomomorphism B'₁ B''₁)
                            (g₂ : Bimodulehomomorphism B₂ B'₂) (g₁ : Bimodulehomomorphism B₁ B'₁) where

  open Monad M₁ using () renaming (C to C₁)
  open Monad M₃ using () renaming (C to C₃)
    
  ⊗₁-distr-∘ᵥ∘arr : α (bimodule-hom-∘ h₂ g₂ ⊗₁ bimodule-hom-∘ h₁ g₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)
                    ≈ (α (h₂ ⊗₁ h₁) ∘ᵥ α (g₂ ⊗₁ g₁)) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)
  ⊗₁-distr-∘ᵥ∘arr = begin
    α (bimodule-hom-∘ h₂ g₂ ⊗₁ bimodule-hom-∘ h₁ g₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ≈⟨ ⟺ αSq ⟩
    Coequalizer.arr (CoeqBimods B''₂ B''₁) ∘ᵥ ((α h₂ ∘ᵥ α g₂) ⊚₁
      ((α h₁ ∘ᵥ Bimodulehomomorphism.α g₁))) ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-⊚ ⟩
    Coequalizer.arr (CoeqBimods B''₂ B''₁) ∘ᵥ (α h₂ ⊚₁ α h₁)
      ∘ᵥ (α g₂ ⊚₁ α g₁) ≈⟨ glue′ (hom C₁ C₃) αʰSq αᵍSq ⟩
    (α (h₂ ⊗₁ h₁) ∘ᵥ α (g₂ ⊗₁ g₁)) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ∎
    where
      open hom.HomReasoning
      open import Categories.Morphism.Reasoning.Core -- TODO
      open TensorproductOfHomomorphisms {B₂ = B₂} {B''₂} {B₁} {B''₁} (bimodule-hom-∘ h₂ g₂) (bimodule-hom-∘ h₁ g₁) using (αSq)
      open TensorproductOfHomomorphisms {B₂ = B'₂} {B''₂} {B'₁} {B''₁} h₂ h₁ using () renaming (αSq to αʰSq)
      open TensorproductOfHomomorphisms {B₂ = B₂} {B'₂} {B₁} {B'₁} g₂ g₁ using () renaming (αSq to αᵍSq)

  ⊗₁-distr-∘ᵥ : α (bimodule-hom-∘ h₂ g₂ ⊗₁ bimodule-hom-∘ h₁ g₁)
                ≈ α (h₂ ⊗₁ h₁) ∘ᵥ α (g₂ ⊗₁ g₁)
  ⊗₁-distr-∘ᵥ = Coequalizer⇒Epi (hom C₁ C₃) (CoeqBimods B₂ B₁)
                                (α (bimodule-hom-∘ h₂ g₂ ⊗₁ bimodule-hom-∘ h₁ g₁))
                                (α (h₂ ⊗₁ h₁) ∘ᵥ α (g₂ ⊗₁ g₁))
                                ⊗₁-distr-∘ᵥ∘arr

module ≈Preservation {M₁ M₂ M₃ : Monad 𝒞} {B₂ B'₂ : Bimodule M₂ M₃} {B₁ B'₁ : Bimodule M₁ M₂}
                            (h₂ h'₂ : Bimodulehomomorphism B₂ B'₂) (h₁ h'₁ : Bimodulehomomorphism B₁ B'₁)
                            (e₂ : α h₂ ≈ α h'₂) (e₁ : α h₁ ≈ α h'₁) where

  open Monad M₁ using () renaming (C to C₁)
  open Monad M₃ using () renaming (C to C₃)

  ⊗₁-resp-≈∘arr : α (h₂ ⊗₁ h₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ≈ α (h'₂ ⊗₁ h'₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)
  ⊗₁-resp-≈∘arr = begin
    α (h₂ ⊗₁ h₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ≈⟨ ⟺ αSq ⟩
    Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α h₂ ⊚₁ α h₁) ≈⟨ refl⟩∘⟨ e₂ ⟩⊚⟨ e₁ ⟩
    Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α h'₂ ⊚₁ α h'₁) ≈⟨ α'Sq ⟩
    α (h'₂ ⊗₁ h'₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ∎
    where
      open hom.HomReasoning
      open TensorproductOfHomomorphisms h₂ h₁ using (αSq)
      open TensorproductOfHomomorphisms h'₂ h'₁ using () renaming (αSq to α'Sq)

  ⊗₁-resp-≈ : α (h₂ ⊗₁ h₁) ≈ α (h'₂ ⊗₁ h'₁)
  ⊗₁-resp-≈ = Coequalizer⇒Epi (hom C₁ C₃) ((CoeqBimods B₂ B₁))
                              (α (h₂ ⊗₁ h₁)) (α (h'₂ ⊗₁ h'₁)) (⊗₁-resp-≈∘arr)
