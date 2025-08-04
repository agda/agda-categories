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

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands

open LocalCoequalizers localCoeq
open ComposeWithLocalCoequalizer 𝒞 localCoeq using (_coeq-◁_; _▷-coeq_)

open Monad using (C; T; μ; η)
open Bimodule using (F; actionˡ; actionʳ)
open Bimodulehomomorphism using (α; linearˡ; linearʳ)

open import Categories.Diagram.Coequalizer (hom (C M₁) (C M₃)) using (Coequalizer; Coequalizer⇒Epi)
open Coequalizer using (arr)
open import Categories.Diagram.Coequalizer.Properties (hom (C M₁) (C M₃)) using (⇒MapBetweenCoeq; ⇒MapBetweenCoeqSq)
import Categories.Category
open Categories.Category.Definitions (hom (C M₁) (C M₃)) using (CommutativeSquare)

import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} {M₁} {M₂} {M₃} as TensorproductOfBimodules
open TensorproductOfBimodules using (CoeqBimods; act-to-the-left; act-to-the-right; F-⊗) renaming (Tensorproduct to infixr 30 _⊗₀_)
open TensorproductOfBimodules.Left-Action using (actionˡ-⊗)
open TensorproductOfBimodules.Right-Action using (actionʳ-⊗)

private
  sq-act-to-the-left : CommutativeSquare
                         (α h₂ ⊚₁ id₂ ⊚₁ α h₁)
                         (act-to-the-left B₂ B₁)
                         (act-to-the-left B'₂ B'₁)
                         (α h₂ ⊚₁ α h₁)
  sq-act-to-the-left = begin
    (act-to-the-left B'₂ B'₁) ∘ᵥ α h₂ ⊚₁ id₂ ⊚₁ α h₁ ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩
    (id₂ ∘ᵥ α h₂) ⊚₁ (actionʳ B'₁ ∘ᵥ id₂ ⊚₁ α h₁) ≈⟨ identity₂ˡ ⟩⊚⟨ linearʳ h₁ ⟩
    α h₂ ⊚₁ (α h₁ ∘ᵥ actionʳ B₁) ≈⟨ ⟺ identity₂ʳ ⟩⊚⟨refl ⟩
    (α h₂ ∘ᵥ id₂) ⊚₁ (α h₁ ∘ᵥ actionʳ B₁) ≈⟨ ∘ᵥ-distr-⊚ ⟩
    α h₂ ⊚₁ α h₁ ∘ᵥ (act-to-the-left B₂ B₁) ∎
    where
      open hom.HomReasoning

  sq-act-to-the-right : CommutativeSquare
                          (α h₂ ⊚₁ id₂ ⊚₁ α h₁)
                          (act-to-the-right B₂ B₁)
                          (act-to-the-right B'₂ B'₁)
                          (α h₂ ⊚₁ α h₁)
  sq-act-to-the-right = begin
    (act-to-the-right B'₂ B'₁) ∘ᵥ α h₂ ⊚₁ id₂ ⊚₁ α h₁ ≈⟨ assoc₂ ⟩
    actionˡ B'₂ ◁ F B'₁ ∘ᵥ α⇐ ∘ᵥ α h₂ ⊚₁ id₂ ⊚₁ α h₁ ≈⟨ refl⟩∘⟨ α⇐-⊚ ⟩
    actionˡ B'₂ ◁ F B'₁ ∘ᵥ (α h₂ ⊚₁ id₂) ⊚₁ α h₁ ∘ᵥ α⇐ ≈⟨ ⟺ assoc₂ ⟩
    (actionˡ B'₂ ◁ F B'₁ ∘ᵥ (α h₂ ⊚₁ id₂) ⊚₁ α h₁) ∘ᵥ α⇐ ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
    ((actionˡ B'₂ ∘ᵥ (α h₂ ⊚₁ id₂)) ⊚₁ (id₂ ∘ᵥ α h₁)) ∘ᵥ α⇐ ≈⟨ linearˡ h₂ ⟩⊚⟨refl ⟩∘⟨refl ⟩
    ((α h₂ ∘ᵥ actionˡ B₂) ⊚₁ (id₂ ∘ᵥ α h₁)) ∘ᵥ α⇐ ≈⟨ refl⟩⊚⟨ identity₂ˡ ⟩∘⟨refl ⟩
    ((α h₂ ∘ᵥ actionˡ B₂) ⊚₁ α h₁) ∘ᵥ α⇐ ≈⟨ refl⟩⊚⟨ ⟺ identity₂ʳ ⟩∘⟨refl ⟩
    ((α h₂ ∘ᵥ actionˡ B₂) ⊚₁ (α h₁ ∘ᵥ id₂)) ∘ᵥ α⇐ ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
    (α h₂ ⊚₁ α h₁ ∘ᵥ actionˡ B₂ ◁ F B₁) ∘ᵥ α⇐ ≈⟨ assoc₂ ⟩
    α h₂ ⊚₁ α h₁ ∘ᵥ (act-to-the-right B₂ B₁) ∎
    where
      open hom.HomReasoning

abstract
  -- to speed-up type-echecking we hide the the underliying 2-cell α-⊗ under an abstract clause --
  -- probably, no one ever wants to look into its defintion and instead only use the lemma αSq-⊗ below --
  α-⊗ : F-⊗ B₂ B₁ ⇒₂ F-⊗ B'₂ B'₁
  α-⊗ = ⇒MapBetweenCoeq
          (α h₂ ⊚₁ id₂ ⊚₁  α h₁)
          (α h₂ ⊚₁ α h₁)
          sq-act-to-the-left
          sq-act-to-the-right
          (CoeqBimods B₂ B₁)
          (CoeqBimods B'₂ B'₁)

  αSq-⊗ : CommutativeSquare
            (α h₂ ⊚₁ α h₁)
            (arr (CoeqBimods B₂ B₁))
            (arr (CoeqBimods B'₂ B'₁))
            α-⊗
  αSq-⊗ = ⇒MapBetweenCoeqSq
            (α h₂ ⊚₁ id₂ ⊚₁  α h₁)
            (α h₂ ⊚₁ α h₁)
            sq-act-to-the-left
            sq-act-to-the-right
            (CoeqBimods B₂ B₁)
            (CoeqBimods B'₂ B'₁)
-- end abstract --


  -- to speed up type-checking we hide the proof of linearity under several small abstract clause --
  abstract
    open TensorproductOfBimodules.Left-Action using (actionˡ-∘)

    linearˡ-∘ :   (actionˡ-∘ B'₂ B'₁) ∘ᵥ (α h₂ ⊚₁ α h₁) ◁ T M₁ ≈ (α h₂ ⊚₁ α h₁) ∘ᵥ  (actionˡ-∘ B₂ B₁)
    linearˡ-∘ = begin
       (actionˡ-∘ B'₂ B'₁) ∘ᵥ (α h₂ ⊚₁ α h₁) ◁ T M₁ ≈⟨ assoc₂ ⟩
      F B'₂ ▷ actionˡ B'₁ ∘ᵥ α⇒ ∘ᵥ (α h₂ ⊚₁ α h₁) ◁ T M₁ ≈⟨ refl⟩∘⟨ α⇒-⊚ ⟩
      F B'₂ ▷ actionˡ B'₁ ∘ᵥ α h₂ ⊚₁ (α h₁ ◁ T M₁) ∘ᵥ α⇒ ≈⟨ ⟺ assoc₂ ⟩
      (F B'₂ ▷ actionˡ B'₁ ∘ᵥ α h₂ ⊚₁ (α h₁ ◁ T M₁)) ∘ᵥ α⇒ ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
      ((id₂ ∘ᵥ α h₂) ⊚₁ (actionˡ B'₁ ∘ᵥ α h₁ ◁ T M₁)) ∘ᵥ α⇒ ≈⟨ identity₂ˡ ⟩⊚⟨ linearˡ h₁ ⟩∘⟨refl ⟩
      (α h₂ ⊚₁ (α h₁ ∘ᵥ actionˡ B₁)) ∘ᵥ α⇒ ≈⟨ ⟺ identity₂ʳ ⟩⊚⟨refl ⟩∘⟨refl ⟩
      ((α h₂ ∘ᵥ id₂) ⊚₁ (α h₁ ∘ᵥ actionˡ B₁)) ∘ᵥ α⇒ ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
      ((α h₂ ⊚₁ α h₁) ∘ᵥ F B₂ ▷ actionˡ B₁) ∘ᵥ α⇒ ≈⟨ assoc₂ ⟩
      (α h₂ ⊚₁ α h₁) ∘ᵥ  (actionˡ-∘ B₂ B₁) ∎
      where
        open hom.HomReasoning

  abstract
    linearˡ-⊗-∘arr : (actionˡ-⊗ B'₂ B'₁ ∘ᵥ α-⊗ ◁ T M₁) ∘ᵥ arr (CoeqBimods B₂ B₁ coeq-◁ T M₁)
                   ≈ (α-⊗ ∘ᵥ actionˡ-⊗ B₂ B₁) ∘ᵥ arr (CoeqBimods B₂ B₁ coeq-◁ T M₁)
    linearˡ-⊗-∘arr = begin
      (actionˡ-⊗ B'₂ B'₁ ∘ᵥ α-⊗ ◁ T M₁) ∘ᵥ arr (CoeqBimods B₂ B₁ coeq-◁ T M₁) ≈⟨ assoc₂ ⟩
      actionˡ-⊗ B'₂ B'₁ ∘ᵥ α-⊗ ◁ T M₁ ∘ᵥ arr (CoeqBimods B₂ B₁ coeq-◁ T M₁) ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ B'₂ B'₁ ∘ᵥ (α-⊗ ∘ᵥ arr (CoeqBimods B₂ B₁)) ◁ T M₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ (⟺ αSq-⊗) ⟩
      actionˡ-⊗ B'₂ B'₁ ∘ᵥ (arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α h₂ ⊚₁ α h₁)) ◁ T M₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ B'₂ B'₁ ∘ᵥ arr (CoeqBimods B'₂ B'₁) ◁ T M₁ ∘ᵥ (α h₂ ⊚₁ α h₁) ◁ T M₁ ≈⟨ ⟺ assoc₂ ⟩
      (actionˡ-⊗ B'₂ B'₁ ∘ᵥ arr (CoeqBimods B'₂ B'₁) ◁ T M₁) ∘ᵥ (α h₂ ⊚₁ α h₁) ◁ T M₁ ≈⟨ ⟺ (actionˡSq-⊗ B'₂ B'₁) ⟩∘⟨refl ⟩
      (arr (CoeqBimods B'₂ B'₁) ∘ᵥ  (actionˡ-∘ B'₂ B'₁)) ∘ᵥ (α h₂ ⊚₁ α h₁) ◁ T M₁ ≈⟨ assoc₂ ⟩
      arr (CoeqBimods B'₂ B'₁) ∘ᵥ  (actionˡ-∘ B'₂ B'₁) ∘ᵥ (α h₂ ⊚₁ α h₁) ◁ T M₁ ≈⟨ refl⟩∘⟨ linearˡ-∘ ⟩
      arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α h₂ ⊚₁ α h₁) ∘ᵥ  (actionˡ-∘ B₂ B₁) ≈⟨ ⟺ assoc₂ ⟩
      (arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α h₂ ⊚₁ α h₁)) ∘ᵥ  (actionˡ-∘ B₂ B₁) ≈⟨ αSq-⊗ ⟩∘⟨refl ⟩
      (α-⊗ ∘ᵥ arr (CoeqBimods B₂ B₁)) ∘ᵥ  (actionˡ-∘ B₂ B₁) ≈⟨ assoc₂ ⟩
      α-⊗ ∘ᵥ arr (CoeqBimods B₂ B₁) ∘ᵥ  (actionˡ-∘ B₂ B₁) ≈⟨ refl⟩∘⟨ actionˡSq-⊗ B₂ B₁ ⟩
      α-⊗ ∘ᵥ actionˡ-⊗ B₂ B₁ ∘ᵥ arr (CoeqBimods B₂ B₁ coeq-◁ T M₁) ≈⟨ ⟺ assoc₂ ⟩
      (α-⊗ ∘ᵥ actionˡ-⊗ B₂ B₁) ∘ᵥ arr (CoeqBimods B₂ B₁ coeq-◁ T M₁) ∎
      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Left-Action using (actionˡSq-⊗)

  abstract
    linearˡ-⊗ : actionˡ-⊗ B'₂ B'₁ ∘ᵥ α-⊗ ◁ T M₁ ≈ α-⊗ ∘ᵥ actionˡ-⊗ B₂ B₁
    linearˡ-⊗ = Coequalizer⇒Epi
                  (CoeqBimods B₂ B₁ coeq-◁ T M₁)
                  (actionˡ-⊗ B'₂ B'₁ ∘ᵥ α-⊗ ◁ T M₁)
                  (α-⊗ ∘ᵥ actionˡ-⊗ B₂ B₁)
                  linearˡ-⊗-∘arr

  open TensorproductOfBimodules.Right-Action using (actionʳ-∘)

  abstract
    linearʳ-∘ : actionʳ-∘ B'₂ B'₁ ∘ᵥ T M₃ ▷ (α h₂ ⊚₁ α h₁) ≈ (α h₂ ⊚₁ α h₁) ∘ᵥ actionʳ-∘ B₂ B₁
    linearʳ-∘ = begin
      actionʳ-∘ B'₂ B'₁ ∘ᵥ T M₃ ▷ (α h₂ ⊚₁ α h₁) ≈⟨ assoc₂ ⟩
      actionʳ B'₂ ◁ F B'₁ ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ (α h₂ ⊚₁ α h₁) ≈⟨ refl⟩∘⟨ α⇐-⊚ ⟩
      actionʳ B'₂ ◁ F B'₁ ∘ᵥ ((T M₃ ▷ α h₂) ⊚₁ α h₁) ∘ᵥ α⇐ ≈⟨ ⟺ assoc₂ ⟩
      (actionʳ B'₂ ◁ F B'₁ ∘ᵥ ((T M₃ ▷ α h₂) ⊚₁ α h₁)) ∘ᵥ α⇐ ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
      ((actionʳ B'₂ ∘ᵥ T M₃ ▷ α h₂) ⊚₁ (id₂ ∘ᵥ α h₁)) ∘ᵥ α⇐ ≈⟨ linearʳ h₂ ⟩⊚⟨ identity₂ˡ ⟩∘⟨refl ⟩
      ((α h₂ ∘ᵥ actionʳ B₂) ⊚₁ α h₁) ∘ᵥ α⇐ ≈⟨ refl⟩⊚⟨ ⟺ identity₂ʳ ⟩∘⟨refl ⟩
      ((α h₂ ∘ᵥ actionʳ B₂) ⊚₁ (α h₁ ∘ᵥ id₂)) ∘ᵥ α⇐ ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
      ((α h₂ ⊚₁ α h₁) ∘ᵥ actionʳ B₂ ◁ F B₁) ∘ᵥ α⇐ ≈⟨ assoc₂ ⟩
      (α h₂ ⊚₁ α h₁) ∘ᵥ actionʳ-∘ B₂ B₁ ∎
      where
        open hom.HomReasoning

  abstract
    linearʳ-⊗-∘arr : (actionʳ-⊗ B'₂ B'₁ ∘ᵥ T M₃ ▷ α-⊗) ∘ᵥ arr (T M₃ ▷-coeq CoeqBimods B₂ B₁)
                   ≈ (α-⊗ ∘ᵥ actionʳ-⊗ B₂ B₁) ∘ᵥ arr (T M₃ ▷-coeq CoeqBimods B₂ B₁)
    linearʳ-⊗-∘arr = begin
      (actionʳ-⊗ B'₂ B'₁ ∘ᵥ T M₃ ▷ α-⊗) ∘ᵥ arr (T M₃ ▷-coeq CoeqBimods B₂ B₁) ≈⟨ assoc₂ ⟩
      actionʳ-⊗ B'₂ B'₁ ∘ᵥ T M₃ ▷ α-⊗ ∘ᵥ arr (T M₃ ▷-coeq CoeqBimods B₂ B₁) ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
      actionʳ-⊗ B'₂ B'₁ ∘ᵥ T M₃ ▷ (α-⊗ ∘ᵥ arr (CoeqBimods B₂ B₁)) ≈⟨ refl⟩∘⟨ ▷-resp-≈ (⟺ αSq-⊗) ⟩
      actionʳ-⊗ B'₂ B'₁ ∘ᵥ T M₃ ▷ (arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α h₂ ⊚₁ α h₁)) ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩
      actionʳ-⊗ B'₂ B'₁ ∘ᵥ T M₃ ▷ arr (CoeqBimods B'₂ B'₁) ∘ᵥ T M₃ ▷ (α h₂ ⊚₁ α h₁) ≈⟨ ⟺ assoc₂ ⟩
      (actionʳ-⊗ B'₂ B'₁ ∘ᵥ T M₃ ▷ arr (CoeqBimods B'₂ B'₁)) ∘ᵥ T M₃ ▷ (α h₂ ⊚₁ α h₁) ≈⟨ ⟺ (actionʳSq-⊗ B'₂ B'₁) ⟩∘⟨refl ⟩
      (arr (CoeqBimods B'₂ B'₁) ∘ᵥ actionʳ-∘ B'₂ B'₁) ∘ᵥ T M₃ ▷ (α h₂ ⊚₁ α h₁) ≈⟨ assoc₂ ⟩
      arr (CoeqBimods B'₂ B'₁) ∘ᵥ actionʳ-∘ B'₂ B'₁ ∘ᵥ T M₃ ▷ (α h₂ ⊚₁ α h₁) ≈⟨ refl⟩∘⟨ linearʳ-∘ ⟩
      arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α h₂ ⊚₁ α h₁) ∘ᵥ actionʳ-∘ B₂ B₁ ≈⟨ ⟺ assoc₂ ⟩
      (arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α h₂ ⊚₁ α h₁)) ∘ᵥ actionʳ-∘ B₂ B₁ ≈⟨ αSq-⊗ ⟩∘⟨refl ⟩
      (α-⊗ ∘ᵥ arr (CoeqBimods B₂ B₁)) ∘ᵥ actionʳ-∘ B₂ B₁ ≈⟨ assoc₂ ⟩
      α-⊗ ∘ᵥ arr (CoeqBimods B₂ B₁) ∘ᵥ actionʳ-∘ B₂ B₁ ≈⟨ refl⟩∘⟨ actionʳSq-⊗ B₂ B₁ ⟩
      α-⊗ ∘ᵥ actionʳ-⊗ B₂ B₁ ∘ᵥ arr (T M₃ ▷-coeq CoeqBimods B₂ B₁) ≈⟨ ⟺ assoc₂ ⟩
      (α-⊗ ∘ᵥ actionʳ-⊗ B₂ B₁) ∘ᵥ arr (T M₃ ▷-coeq CoeqBimods B₂ B₁) ∎
      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Right-Action using (actionʳSq-⊗)

  abstract
    linearʳ-⊗ : actionʳ-⊗ B'₂ B'₁ ∘ᵥ T M₃ ▷ α-⊗ ≈ α-⊗ ∘ᵥ actionʳ-⊗ B₂ B₁
    linearʳ-⊗ = Coequalizer⇒Epi
                  (T M₃ ▷-coeq CoeqBimods B₂ B₁)
                  (actionʳ-⊗ B'₂ B'₁ ∘ᵥ T M₃ ▷ α-⊗)
                  (α-⊗ ∘ᵥ actionʳ-⊗ B₂ B₁)
                  linearʳ-⊗-∘arr

  -- end abstract --

Tensorproduct : Bimodulehomomorphism (B₂ ⊗₀ B₁) (B'₂ ⊗₀ B'₁)
Tensorproduct = record
  { α = α-⊗
  ; linearˡ = linearˡ-⊗
  ; linearʳ = linearʳ-⊗
  }
