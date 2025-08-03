{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers
open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism using (Bimodulehomomorphism)

module Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞}
  {M₁ M₂ M₃ : Monad 𝒞} {B₂ B'₂ : Bimodule M₂ M₃} {B₁ B'₁ : Bimodule M₁ M₂}
  (h₂ : Bimodulehomomorphism B₂ B'₂) (h₁ : Bimodulehomomorphism B₁ B'₁) where

open import Level
import Categories.Category.Construction.Bimodules
open Categories.Category.Construction.Bimodules {o} {ℓ} {e} {t} {𝒞} renaming (Bimodules to Bimodules₁)
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open import Categories.Category
open import Categories.Diagram.Coequalizer
import Categories.Diagram.Coequalizer.Properties as CoeqProperties

private
  module Bimodules₁ M₁ M₂ = Category (Bimodules₁ M₁ M₂)

open LocalCoequalizers localCoeq
open ComposeWithLocalCoequalizer 𝒞 localCoeq using (_coeq-◁_; _▷-coeq_)


open Monad M₁ using () renaming (C to C₁; T to T₁; μ to μ₁; η to η₁)
open Monad M₂ using () renaming (C to C₂; T to T₂; μ to μ₂; η to η₂)
open Monad M₃ using () renaming (C to C₃; T to T₃; μ to μ₃; η to η₃)
open Bimodule B₁ using () renaming (F to F₁; actionʳ to actionʳ₁; actionˡ to actionˡ₁)
open Bimodule B'₁ using () renaming (F to F'₁; actionʳ to actionʳ'₁; actionˡ to actionˡ'₁)
open Bimodule B₂ using () renaming (F to F₂; actionʳ to actionʳ₂; actionˡ to actionˡ₂)
open Bimodule B'₂ using () renaming (F to F'₂; actionʳ to actionʳ'₂; actionˡ to actionˡ'₂)

import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} {M₁} {M₂} {M₃} as TensorproductOfBimodules
open TensorproductOfBimodules using (CoeqBimods; act-to-the-left; act-to-the-right; F-⊗) renaming (Tensorproduct to infixr 30 _⊗₀_)
open TensorproductOfBimodules.Left-Action using (actionˡ-⊗)
open TensorproductOfBimodules.Right-Action using (actionʳ-⊗)

open Bimodulehomomorphism h₁ using () renaming (α to α₁; linearˡ to linearˡ₁; linearʳ to linearʳ₁)
open Bimodulehomomorphism h₂ using () renaming (α to α₂; linearˡ to linearˡ₂; linearʳ to linearʳ₂)

open Definitions (hom C₁ C₃) -- for Commutative Squares

private
  sq-act-to-the-left : CommutativeSquare (α₂ ⊚₁ id₂ ⊚₁ α₁)
                          (act-to-the-left B₂ B₁)
                          (act-to-the-left B'₂ B'₁)
                          (α₂ ⊚₁ α₁)
  sq-act-to-the-left = begin
    (act-to-the-left B'₂ B'₁) ∘ᵥ α₂ ⊚₁ id₂ ⊚₁ α₁ ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩
    (id₂ ∘ᵥ α₂) ⊚₁ (actionʳ'₁ ∘ᵥ id₂ ⊚₁ α₁) ≈⟨ identity₂ˡ ⟩⊚⟨ linearʳ₁ ⟩
    α₂ ⊚₁ (α₁ ∘ᵥ actionʳ₁) ≈⟨ ⟺ identity₂ʳ ⟩⊚⟨refl ⟩
    (α₂ ∘ᵥ id₂) ⊚₁ (α₁ ∘ᵥ actionʳ₁) ≈⟨ ∘ᵥ-distr-⊚ ⟩
    α₂ ⊚₁ α₁ ∘ᵥ (act-to-the-left B₂ B₁) ∎
    where
      open hom.HomReasoning

  sq-act-to-the-right : CommutativeSquare (α₂ ⊚₁ id₂ ⊚₁ α₁)
                          (act-to-the-right B₂ B₁)
                          (act-to-the-right B'₂ B'₁)
                          (α₂ ⊚₁ α₁)
  sq-act-to-the-right = begin
    (act-to-the-right B'₂ B'₁) ∘ᵥ α₂ ⊚₁ id₂ ⊚₁ α₁ ≈⟨ assoc₂ ⟩
    actionˡ'₂ ◁ F'₁ ∘ᵥ associator.to ∘ᵥ α₂ ⊚₁ id₂ ⊚₁ α₁ ≈⟨ refl⟩∘⟨ α⇐-⊚ ⟩
    actionˡ'₂ ◁ F'₁ ∘ᵥ (α₂ ⊚₁ id₂) ⊚₁ α₁ ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
    (actionˡ'₂ ◁ F'₁ ∘ᵥ (α₂ ⊚₁ id₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
    ((actionˡ'₂ ∘ᵥ (α₂ ⊚₁ id₂)) ⊚₁ (id₂ ∘ᵥ α₁)) ∘ᵥ associator.to ≈⟨ linearˡ₂ ⟩⊚⟨refl ⟩∘⟨refl ⟩
    ((α₂ ∘ᵥ actionˡ₂) ⊚₁ (id₂ ∘ᵥ α₁)) ∘ᵥ associator.to ≈⟨ refl⟩⊚⟨ identity₂ˡ ⟩∘⟨refl ⟩
    ((α₂ ∘ᵥ actionˡ₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ refl⟩⊚⟨ ⟺ identity₂ʳ ⟩∘⟨refl ⟩
    ((α₂ ∘ᵥ actionˡ₂) ⊚₁ (α₁ ∘ᵥ id₂)) ∘ᵥ associator.to ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
    (α₂ ⊚₁ α₁ ∘ᵥ actionˡ₂ ◁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
    α₂ ⊚₁ α₁ ∘ᵥ (act-to-the-right B₂ B₁) ∎
    where
      open hom.HomReasoning

abstract
  -- to speed-up type-echecking we hide the the underliying 2-cell α-⊗ under an abstract clause --
  -- probably, no one ever wants to look into its defintion and instead only use the lemma αSq-⊗ below --
  α-⊗ : F-⊗ B₂ B₁ ⇒₂ F-⊗ B'₂ B'₁
  α-⊗ = ⇒MapBetweenCoeq (α₂ ⊚₁ id₂ ⊚₁  α₁) (α₂ ⊚₁ α₁) sq-act-to-the-left sq-act-to-the-right (CoeqBimods B₂ B₁) (CoeqBimods B'₂ B'₁)
    where
      open CoeqProperties (hom C₁ C₃)

  αSq-⊗ : CommutativeSquare (α₂ ⊚₁ α₁) (Coequalizer.arr (CoeqBimods B₂ B₁)) (Coequalizer.arr (CoeqBimods B'₂ B'₁)) α-⊗
  αSq-⊗ = ⇒MapBetweenCoeqSq (α₂ ⊚₁ id₂ ⊚₁  α₁) (α₂ ⊚₁ α₁) sq-act-to-the-left sq-act-to-the-right (CoeqBimods B₂ B₁) (CoeqBimods B'₂ B'₁)
    where
      open CoeqProperties (hom C₁ C₃)
-- end abstract --


  -- to speed up type-checking we hide the proof of linearity under several small abstract clause --
  abstract
    open TensorproductOfBimodules.Left-Action using (actionˡ-∘)

    linearˡ-∘ :   (actionˡ-∘ B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈ (α₂ ⊚₁ α₁) ∘ᵥ  (actionˡ-∘ B₂ B₁)
    linearˡ-∘ = begin
       (actionˡ-∘ B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ assoc₂ ⟩
      F'₂ ▷ actionˡ'₁ ∘ᵥ associator.from ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ refl⟩∘⟨ α⇒-⊚ ⟩
      F'₂ ▷ actionˡ'₁ ∘ᵥ α₂ ⊚₁ (α₁ ◁ T₁) ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩
      (F'₂ ▷ actionˡ'₁ ∘ᵥ α₂ ⊚₁ (α₁ ◁ T₁)) ∘ᵥ associator.from ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
      ((id₂ ∘ᵥ α₂) ⊚₁ (actionˡ'₁ ∘ᵥ α₁ ◁ T₁)) ∘ᵥ associator.from ≈⟨ identity₂ˡ ⟩⊚⟨ linearˡ₁ ⟩∘⟨refl ⟩
      (α₂ ⊚₁ (α₁ ∘ᵥ actionˡ₁)) ∘ᵥ associator.from ≈⟨ ⟺ identity₂ʳ ⟩⊚⟨refl ⟩∘⟨refl ⟩
      ((α₂ ∘ᵥ id₂) ⊚₁ (α₁ ∘ᵥ actionˡ₁)) ∘ᵥ associator.from ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
      ((α₂ ⊚₁ α₁) ∘ᵥ F₂ ▷ actionˡ₁) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      (α₂ ⊚₁ α₁) ∘ᵥ  (actionˡ-∘ B₂ B₁) ∎
      where
        open hom.HomReasoning

  abstract
    linearˡ-⊗-∘arr : (actionˡ-⊗ B'₂ B'₁ ∘ᵥ α-⊗ ◁ T₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁ coeq-◁ T₁)
                  ≈ (α-⊗ ∘ᵥ actionˡ-⊗ B₂ B₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁ coeq-◁ T₁)
    linearˡ-⊗-∘arr = begin
      (actionˡ-⊗ B'₂ B'₁ ∘ᵥ α-⊗ ◁ T₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁ coeq-◁ T₁) ≈⟨ assoc₂ ⟩
      actionˡ-⊗ B'₂ B'₁ ∘ᵥ α-⊗ ◁ T₁ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁ coeq-◁ T₁) ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ B'₂ B'₁ ∘ᵥ (α-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ (⟺ αSq-⊗) ⟩
      actionˡ-⊗ B'₂ B'₁ ∘ᵥ (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁)) ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ B'₂ B'₁ ∘ᵥ Coequalizer.arr (CoeqBimods B'₂ B'₁) ◁ T₁ ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ B'₂ B'₁ ∘ᵥ Coequalizer.arr (CoeqBimods B'₂ B'₁) ◁ T₁) ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ ⟺ (actionˡSq-⊗ B'₂ B'₁) ⟩∘⟨refl ⟩
      (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ  (actionˡ-∘ B'₂ B'₁)) ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ assoc₂ ⟩
      Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ  (actionˡ-∘ B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ refl⟩∘⟨ linearˡ-∘ ⟩
      Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁) ∘ᵥ  (actionˡ-∘ B₂ B₁) ≈⟨ sym-assoc₂ ⟩
      (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁)) ∘ᵥ  (actionˡ-∘ B₂ B₁) ≈⟨ αSq-⊗ ⟩∘⟨refl ⟩
      (α-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)) ∘ᵥ  (actionˡ-∘ B₂ B₁) ≈⟨ assoc₂ ⟩
      α-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ∘ᵥ  (actionˡ-∘ B₂ B₁) ≈⟨ refl⟩∘⟨ actionˡSq-⊗ B₂ B₁ ⟩
      α-⊗ ∘ᵥ actionˡ-⊗ B₂ B₁ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁ coeq-◁ T₁) ≈⟨ sym-assoc₂ ⟩
      (α-⊗ ∘ᵥ actionˡ-⊗ B₂ B₁) ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁ coeq-◁ T₁) ∎
      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Left-Action using (actionˡSq-⊗)

  abstract
    linearˡ-⊗ : actionˡ-⊗ B'₂ B'₁ ∘ᵥ α-⊗ ◁ T₁ ≈ α-⊗ ∘ᵥ actionˡ-⊗ B₂ B₁
    linearˡ-⊗ = Coequalizer⇒Epi (hom C₁ C₃) (CoeqBimods B₂ B₁ coeq-◁ T₁)
                            (actionˡ-⊗ B'₂ B'₁ ∘ᵥ α-⊗ ◁ T₁) (α-⊗ ∘ᵥ actionˡ-⊗ B₂ B₁)
                            linearˡ-⊗-∘arr

  open TensorproductOfBimodules.Right-Action using (actionʳ-∘)

  abstract
    linearʳ-∘ : actionʳ-∘ B'₂ B'₁ ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈ (α₂ ⊚₁ α₁) ∘ᵥ actionʳ-∘ B₂ B₁
    linearʳ-∘ = begin
      actionʳ-∘ B'₂ B'₁ ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ assoc₂ ⟩
      actionʳ'₂ ◁ F'₁ ∘ᵥ associator.to ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ refl⟩∘⟨ α⇐-⊚ ⟩
      actionʳ'₂ ◁ F'₁ ∘ᵥ ((T₃ ▷ α₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
      (actionʳ'₂ ◁ F'₁ ∘ᵥ ((T₃ ▷ α₂) ⊚₁ α₁)) ∘ᵥ associator.to ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
      ((actionʳ'₂ ∘ᵥ T₃ ▷ α₂) ⊚₁ (id₂ ∘ᵥ α₁)) ∘ᵥ associator.to ≈⟨ linearʳ₂ ⟩⊚⟨ identity₂ˡ ⟩∘⟨refl ⟩
      ((α₂ ∘ᵥ actionʳ₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ refl⟩⊚⟨ ⟺ identity₂ʳ ⟩∘⟨refl ⟩
      ((α₂ ∘ᵥ actionʳ₂) ⊚₁ (α₁ ∘ᵥ id₂)) ∘ᵥ associator.to ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
      ((α₂ ⊚₁ α₁) ∘ᵥ actionʳ₂ ◁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
      (α₂ ⊚₁ α₁) ∘ᵥ actionʳ-∘ B₂ B₁ ∎
      where
        open hom.HomReasoning

  abstract
    linearʳ-⊗-∘arr : (actionʳ-⊗ B'₂ B'₁ ∘ᵥ T₃ ▷ α-⊗) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq CoeqBimods B₂ B₁)
                ≈ (α-⊗ ∘ᵥ actionʳ-⊗ B₂ B₁) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq CoeqBimods B₂ B₁)
    linearʳ-⊗-∘arr = begin
      (actionʳ-⊗ B'₂ B'₁ ∘ᵥ T₃ ▷ α-⊗) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq CoeqBimods B₂ B₁) ≈⟨ assoc₂ ⟩
      actionʳ-⊗ B'₂ B'₁ ∘ᵥ T₃ ▷ α-⊗ ∘ᵥ Coequalizer.arr (T₃ ▷-coeq CoeqBimods B₂ B₁) ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
      actionʳ-⊗ B'₂ B'₁ ∘ᵥ T₃ ▷ (α-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)) ≈⟨ refl⟩∘⟨ ▷-resp-≈ (⟺ αSq-⊗) ⟩
      actionʳ-⊗ B'₂ B'₁ ∘ᵥ T₃ ▷ (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁)) ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩
      actionʳ-⊗ B'₂ B'₁ ∘ᵥ T₃ ▷ Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ sym-assoc₂ ⟩
      (actionʳ-⊗ B'₂ B'₁ ∘ᵥ T₃ ▷ Coequalizer.arr (CoeqBimods B'₂ B'₁)) ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ ⟺ (actionʳSq-⊗ B'₂ B'₁) ⟩∘⟨refl ⟩
      (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ actionʳ-∘ B'₂ B'₁) ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ assoc₂ ⟩
      Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ actionʳ-∘ B'₂ B'₁ ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ refl⟩∘⟨ linearʳ-∘ ⟩
      Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁) ∘ᵥ actionʳ-∘ B₂ B₁ ≈⟨ sym-assoc₂ ⟩
      (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁)) ∘ᵥ actionʳ-∘ B₂ B₁ ≈⟨ αSq-⊗ ⟩∘⟨refl ⟩
      (α-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)) ∘ᵥ actionʳ-∘ B₂ B₁ ≈⟨ assoc₂ ⟩
      α-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ∘ᵥ actionʳ-∘ B₂ B₁ ≈⟨ refl⟩∘⟨ actionʳSq-⊗ B₂ B₁ ⟩
      α-⊗ ∘ᵥ actionʳ-⊗ B₂ B₁ ∘ᵥ Coequalizer.arr (T₃ ▷-coeq CoeqBimods B₂ B₁) ≈⟨ sym-assoc₂ ⟩
      (α-⊗ ∘ᵥ actionʳ-⊗ B₂ B₁) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq CoeqBimods B₂ B₁) ∎
      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Right-Action using (actionʳSq-⊗)

  abstract
    linearʳ-⊗ : actionʳ-⊗ B'₂ B'₁ ∘ᵥ T₃ ▷ α-⊗ ≈ α-⊗ ∘ᵥ actionʳ-⊗ B₂ B₁
    linearʳ-⊗ = Coequalizer⇒Epi (hom C₁ C₃) (T₃ ▷-coeq CoeqBimods B₂ B₁)
                              (actionʳ-⊗ B'₂ B'₁ ∘ᵥ T₃ ▷ α-⊗) (α-⊗ ∘ᵥ actionʳ-⊗ B₂ B₁)
                              linearʳ-⊗-∘arr

  -- end abstract --

Tensorproduct : Bimodulehomomorphism (B₂ ⊗₀ B₁) (B'₂ ⊗₀ B'₁)
Tensorproduct = record
  { α = α-⊗
  ; linearˡ = linearˡ-⊗
  ; linearʳ = linearʳ-⊗
  }
