{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers
open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule

module Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞}
  {M₁ M₂ M₃ : Monad 𝒞} (B₂ : Bimodule M₂ M₃) (B₁ : Bimodule M₁ M₂) where

open import Level
open import Categories.Bicategory.Monad.Bimodule.Homomorphism using (Bimodulehomomorphism)
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
open Bimodule B₁ using ()
  renaming (F to F₁; actionˡ to actionˡ₁; actionʳ to actionʳ₁; assoc to action-assoc₁;
            sym-assoc to action-sym-assoc₁; assoc-actionˡ to assoc-actionˡ₁; identityˡ to identityˡ₁)
open Bimodule B₂ using ()
  renaming (F to F₂; actionˡ to actionˡ₂; actionʳ to actionʳ₂; assoc to action-assoc₂;
            sym-assoc to action-sym-assoc₂; assoc-actionʳ to assoc-actionʳ₂; identityʳ to identityʳ₂)

{-
To construct the tensorproduct B₂⊗B₁ we will define its underlying 1-cell
to be the coequalizer of the following parallel pair in hom C₁ C₃:

                      act-to-the-left
  F B₂ ∘ T M₂ ∘ F B₁ ==================> F B₂ ∘ F B₁
                      act-to-the-right
-}

-- We itroduce names to the two parallel morphism in the above diagram --
act-to-the-left act-to-the-right : F₂ ∘₁ T₂ ∘₁ F₁ ⇒₂ F₂ ∘₁ F₁
act-to-the-left = F₂ ▷ actionʳ₁
act-to-the-right = actionˡ₂ ◁ F₁ ∘ᵥ associator.to


-- The coequalizer that defines the composite bimodule --
CoeqBimods : Coequalizer (hom C₁ C₃) (act-to-the-left) (act-to-the-right)
CoeqBimods = localCoequalizers C₁ C₃ (act-to-the-left) (act-to-the-right)
-- coequalizer {_} {_} {F₂ ∘₁ T₂ ∘₁ F₁} {F₂ ∘₁ F₁} (act-to-the-left) (act-to-the-right)

-- The underlying object of that coequalizer is the underlying 1-cell of the bimodule B₂⊗B₁ --
F-⊗ : C₁ ⇒₁ C₃
F-⊗ = Coequalizer.obj CoeqBimods


module Left-Action where

  {-
                                 act-to-the-left ◁ T M₁
    (F B₂ ∘ T M₂ ∘ F B₁) ∘ T M₁ ========================> (F B₂ ∘ F B₁) ∘ T M₁ ---> F ∘ T M₁      ::     CoeqBimods
             |                   act-to-the-right ◁ T M₁            |                  .
             |                                                      |                  .
         actionˡ-∘-∘                                             actionˡ-∘          actionˡ-⊗
             |                                                      |                  .
             v                      act-to-the-left                 v                  v
    F B₂ ∘ T M₂ ∘ F M₁ ======================================> F B₂ ∘ F B₁ ----------> F          ::     CoeqBimods coeq-◁ T M₁
                                    act-to-the-right
  -}

  actionˡ-∘-∘ : (F₂ ∘₁ T₂ ∘₁ F₁) ∘₁ T₁ ⇒₂ F₂ ∘₁ T₂ ∘₁ F₁
  actionˡ-∘-∘ = associator.from ∘ᵥ (F₂ ∘₁ T₂) ▷ actionˡ₁ ∘ᵥ associator.from  ∘ᵥ associator.to ◁ T₁

  actionˡ-∘ : (F₂ ∘₁ F₁) ∘₁ T₁ ⇒₂  F₂ ∘₁ F₁
  actionˡ-∘ = F₂ ▷ actionˡ₁ ∘ᵥ associator.from

  -- for CommutativeSquare --
  open Definitions (hom C₁ C₃)

  abstract
    sq₁ : CommutativeSquare (actionˡ-∘-∘) ((act-to-the-left) ◁ T₁) (act-to-the-left) (actionˡ-∘)
    sq₁ = begin
      act-to-the-left ∘ᵥ actionˡ-∘-∘                                     ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      F₂ ▷ actionʳ₁ ∘ᵥ (associator.from ∘ᵥ (F₂ ∘₁ T₂) ▷ actionˡ₁)
        ∘ᵥ associator.from  ∘ᵥ associator.to ◁ T₁                          ≈⟨ refl⟩∘⟨ α⇒-▷-∘₁ ⟩∘⟨refl ⟩
      F₂ ▷ actionʳ₁ ∘ᵥ (F₂ ▷ T₂ ▷ actionˡ₁ ∘ᵥ associator.from)
        ∘ᵥ associator.from  ∘ᵥ associator.to ◁ T₁                          ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      F₂ ▷ actionʳ₁ ∘ᵥ F₂ ▷ T₂ ▷ actionˡ₁ ∘ᵥ associator.from
        ∘ᵥ associator.from  ∘ᵥ associator.to ◁ T₁                          ≈⟨ sym-assoc₂ ⟩
      (F₂ ▷ actionʳ₁ ∘ᵥ F₂ ▷ T₂ ▷ actionˡ₁) ∘ᵥ associator.from
        ∘ᵥ associator.from  ∘ᵥ associator.to ◁ T₁                          ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      (F₂ ▷ actionʳ₁ ∘ᵥ F₂ ▷ T₂ ▷ actionˡ₁) ∘ᵥ (associator.from
        ∘ᵥ associator.from)  ∘ᵥ associator.to ◁ T₁                         ≈⟨ refl⟩∘⟨ ⟺ pentagon ⟩∘⟨refl ⟩
      -- maybe this can be shortened using conjugate --
      (F₂ ▷ actionʳ₁ ∘ᵥ F₂ ▷ T₂ ▷ actionˡ₁) ∘ᵥ (F₂ ▷ associator.from
        ∘ᵥ associator.from ∘ᵥ associator.from ◁ T₁) ∘ᵥ associator.to ◁ T₁  ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      (F₂ ▷ actionʳ₁ ∘ᵥ F₂ ▷ T₂ ▷ actionˡ₁) ∘ᵥ F₂ ▷ associator.from
        ∘ᵥ (associator.from ∘ᵥ associator.from ◁ T₁) ∘ᵥ associator.to ◁ T₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩
      (F₂ ▷ actionʳ₁ ∘ᵥ F₂ ▷ T₂ ▷ actionˡ₁) ∘ᵥ F₂ ▷ associator.from
        ∘ᵥ associator.from ∘ᵥ associator.from ◁ T₁ ∘ᵥ associator.to ◁ T₁   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      (F₂ ▷ actionʳ₁ ∘ᵥ F₂ ▷ T₂ ▷ actionˡ₁) ∘ᵥ F₂ ▷ associator.from
        ∘ᵥ associator.from ∘ᵥ (associator.from ∘ᵥ associator.to) ◁ T₁      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ◁-resp-≈ associator.isoʳ ⟩
      (F₂ ▷ actionʳ₁ ∘ᵥ F₂ ▷ T₂ ▷ actionˡ₁) ∘ᵥ F₂ ▷ associator.from
        ∘ᵥ associator.from ∘ᵥ id₂ ◁ T₁                                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ id₂◁ ⟩
      (F₂ ▷ actionʳ₁ ∘ᵥ F₂ ▷ T₂ ▷ actionˡ₁) ∘ᵥ F₂ ▷ associator.from
        ∘ᵥ associator.from ∘ᵥ id₂                                          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ identity₂ʳ ⟩
      (F₂ ▷ actionʳ₁ ∘ᵥ F₂ ▷ T₂ ▷ actionˡ₁) ∘ᵥ F₂ ▷ associator.from
        ∘ᵥ associator.from                                                 ≈⟨ sym-assoc₂ ⟩
      ((F₂ ▷ actionʳ₁ ∘ᵥ F₂ ▷ T₂ ▷ actionˡ₁) ∘ᵥ F₂ ▷ associator.from)
        ∘ᵥ associator.from                                                 ≈⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩∘⟨refl ⟩
      (F₂ ▷ (actionʳ₁ ∘ᵥ T₂ ▷ actionˡ₁) ∘ᵥ F₂ ▷ associator.from)
        ∘ᵥ associator.from                                                 ≈⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
      F₂ ▷ ((actionʳ₁ ∘ᵥ T₂ ▷ actionˡ₁) ∘ᵥ associator.from)
        ∘ᵥ associator.from                                                 ≈⟨ ▷-resp-≈ assoc₂ ⟩∘⟨refl ⟩
      F₂ ▷ (actionʳ₁ ∘ᵥ T₂ ▷ actionˡ₁ ∘ᵥ associator.from)
        ∘ᵥ associator.from ≈⟨ ▷-resp-≈ action-assoc₁ ⟩∘⟨refl ⟩
      F₂ ▷ (actionˡ₁ ∘ᵥ actionʳ₁ ◁ T₁) ∘ᵥ associator.from                  ≈⟨ ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
      (F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ (actionʳ₁ ◁ T₁)) ∘ᵥ associator.from           ≈⟨ assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ (actionʳ₁ ◁ T₁) ∘ᵥ associator.from             ≈⟨ refl⟩∘⟨ ⟺ α⇒-▷-◁ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ associator.from ∘ᵥ (F₂ ▷ actionʳ₁) ◁ T₁             ≈⟨ ⟺ assoc₂ ⟩
      actionˡ-∘ ∘ᵥ (act-to-the-left) ◁ T₁ ∎
      where
        open hom.HomReasoning

    sq₂ : CommutativeSquare (actionˡ-∘-∘) ((act-to-the-right) ◁ T₁) (act-to-the-right) (actionˡ-∘)
    sq₂ = begin
      (act-to-the-right) ∘ᵥ actionˡ-∘-∘                               ≈⟨ sym-assoc₂ ⟩
      ((actionˡ₂ ◁ F₁ ∘ᵥ associator.to) ∘ᵥ associator.from) ∘ᵥ (F₂ ∘₁ T₂) ▷ actionˡ₁
        ∘ᵥ associator.from ∘ᵥ associator.to ◁ T₁                                        ≈⟨ assoc₂ ⟩∘⟨refl ⟩
      (actionˡ₂ ◁ F₁ ∘ᵥ associator.to ∘ᵥ associator.from) ∘ᵥ (F₂ ∘₁ T₂) ▷ actionˡ₁
        ∘ᵥ associator.from ∘ᵥ associator.to ◁ T₁                                        ≈⟨ (refl⟩∘⟨ associator.isoˡ) ⟩∘⟨refl ⟩
      (actionˡ₂ ◁ F₁ ∘ᵥ id₂) ∘ᵥ (F₂ ∘₁ T₂) ▷ actionˡ₁
        ∘ᵥ associator.from ∘ᵥ associator.to ◁ T₁                                        ≈⟨ identity₂ʳ ⟩∘⟨refl ⟩
      actionˡ₂ ◁ F₁ ∘ᵥ (F₂ ∘₁ T₂) ▷ actionˡ₁ ∘ᵥ associator.from ∘ᵥ associator.to ◁ T₁   ≈⟨ sym-assoc₂ ⟩
      (actionˡ₂ ◁ F₁ ∘ᵥ (F₂ ∘₁ T₂) ▷ actionˡ₁) ∘ᵥ associator.from ∘ᵥ associator.to ◁ T₁ ≈⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
      (F₂ ▷ actionˡ₁ ∘ᵥ actionˡ₂ ◁ (F₁ ∘₁ T₁)) ∘ᵥ associator.from ∘ᵥ associator.to ◁ T₁ ≈⟨ assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ actionˡ₂ ◁ (F₁ ∘₁ T₁) ∘ᵥ associator.from ∘ᵥ associator.to ◁ T₁   ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ (actionˡ₂ ◁ (F₁ ∘₁ T₁) ∘ᵥ associator.from) ∘ᵥ associator.to ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ α⇒-◁-∘₁ ⟩∘⟨refl ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ (associator.from ∘ᵥ actionˡ₂ ◁ F₁ ◁ T₁) ∘ᵥ associator.to ◁ T₁    ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ associator.from ∘ᵥ actionˡ₂ ◁ F₁ ◁ T₁ ∘ᵥ associator.to ◁ T₁      ≈⟨ sym-assoc₂ ⟩
      actionˡ-∘ ∘ᵥ actionˡ₂ ◁ F₁ ◁ T₁ ∘ᵥ associator.to ◁ T₁                           ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-∘ ∘ᵥ (act-to-the-right) ◁ T₁ ∎
      where
        open hom.HomReasoning
        open hom.Equiv
  -- end abstract --

  -- left-action --
  actionˡ-⊗ : F-⊗ ∘₁ T₁ ⇒₂ F-⊗
  actionˡ-⊗ = ⇒MapBetweenCoeq actionˡ-∘-∘ actionˡ-∘ sq₁ sq₂ (CoeqBimods coeq-◁ T₁) CoeqBimods
    where
      open CoeqProperties (hom C₁ C₃)

  abstract    
    -- the left-action fits into the following commutative square --
    actionˡSq : CommutativeSquare (actionˡ-∘) (Coequalizer.arr (CoeqBimods coeq-◁ T₁)) (Coequalizer.arr CoeqBimods) (actionˡ-⊗)
    actionˡSq = ⇒MapBetweenCoeqSq actionˡ-∘-∘ actionˡ-∘ sq₁ sq₂ (CoeqBimods coeq-◁ T₁) CoeqBimods
      where
        open CoeqProperties (hom C₁ C₃)
  -- end abstract --

module Right-Action where

  -- To define the right-action we need that T₃ ∘₁ F-⊗ is a coequalizer --
  T₃∘FCoequalizer : Coequalizer (hom C₁ C₃) (T₃ ▷ (act-to-the-left)) (T₃ ▷ (act-to-the-right))
  T₃∘FCoequalizer =  T₃ ▷-coeq CoeqBimods

  -- to define a map between the coequalizers T₃ ∘₁ F-⊗ ⇒₂ F-⊗ we define a map of diagrams --
  actionʳ₂◁T₂∘₁F₁ : T₃ ∘₁ F₂ ∘₁ T₂ ∘₁ F₁ ⇒₂  F₂ ∘₁ T₂ ∘₁ F₁
  actionʳ₂◁T₂∘₁F₁ = actionʳ₂ ◁ (T₂ ∘₁ F₁) ∘ᵥ associator.to

  actionʳ₂◁F₁ : T₃ ∘₁ F₂ ∘₁ F₁ ⇒₂  F₂ ∘₁ F₁
  actionʳ₂◁F₁ = actionʳ₂ ◁ F₁ ∘ᵥ associator.to

  -- for CommutativeSquare --
  open Definitions (hom C₁ C₃)

  -- to get a map of diagrams two squares have to commute --
  abstract
    sq₁ : CommutativeSquare (actionʳ₂◁T₂∘₁F₁) (T₃ ▷ act-to-the-left) (act-to-the-left) (actionʳ₂◁F₁)
    sq₁ = glue′ sq₁bottom sq₁top
      where
        open hom.HomReasoning
        open import Categories.Morphism.Reasoning.Core (hom C₁ C₃)
        sq₁top : CommutativeSquare (associator.to) (T₃ ▷ F₂ ▷ actionʳ₁) ((T₃ ∘₁ F₂) ▷ actionʳ₁) (associator.to)
        sq₁top = ⟺ α⇐-▷-∘₁
        sq₁bottom : CommutativeSquare (actionʳ₂ ◁ (T₂ ∘₁ F₁)) ((T₃ ∘₁ F₂) ▷ actionʳ₁) (F₂ ▷ actionʳ₁) (actionʳ₂ ◁ F₁)
        sq₁bottom = ◁-▷-exchg

    sq₂ : CommutativeSquare (actionʳ₂◁T₂∘₁F₁) (T₃ ▷ (act-to-the-right)) (act-to-the-right) (actionʳ₂◁F₁)
    sq₂ = begin
      (act-to-the-right) ∘ᵥ (actionʳ₂◁T₂∘₁F₁)                            ≈⟨ sym-assoc₂ ⟩
      ((actionˡ₂ ◁ F₁ ∘ᵥ associator.to) ∘ᵥ actionʳ₂ ◁  (T₂ ∘₁ F₁)) ∘ᵥ associator.to    ≈⟨ assoc₂ ⟩∘⟨refl ⟩
      (actionˡ₂ ◁ F₁ ∘ᵥ (associator.to ∘ᵥ actionʳ₂ ◁  (T₂ ∘₁ F₁))) ∘ᵥ associator.to    ≈⟨ (refl⟩∘⟨ α⇐-◁-∘₁) ⟩∘⟨refl ⟩
      (actionˡ₂ ◁ F₁ ∘ᵥ (actionʳ₂ ◁ T₂ ◁ F₁ ∘ᵥ associator.to)) ∘ᵥ associator.to        ≈⟨ assoc₂ ⟩
      actionˡ₂ ◁ F₁ ∘ᵥ ((actionʳ₂ ◁ T₂ ◁ F₁ ∘ᵥ associator.to) ∘ᵥ associator.to)        ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionˡ₂ ◁ F₁ ∘ᵥ actionʳ₂ ◁ T₂ ◁ F₁ ∘ᵥ associator.to ∘ᵥ associator.to            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym pentagon-inv ⟩
      actionˡ₂ ◁ F₁ ∘ᵥ actionʳ₂ ◁ T₂ ◁ F₁ ∘ᵥ (associator.to ◁ F₁ ∘ᵥ associator.to)
        ∘ᵥ T₃ ▷ associator.to                                                          ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionˡ₂ ◁ F₁ ∘ᵥ (actionʳ₂ ◁ T₂ ◁ F₁ ∘ᵥ (associator.to ◁ F₁ ∘ᵥ associator.to))
        ∘ᵥ T₃ ▷ associator.to                                                          ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      actionˡ₂ ◁ F₁ ∘ᵥ ((actionʳ₂ ◁ T₂ ◁ F₁ ∘ᵥ associator.to ◁ F₁) ∘ᵥ associator.to)
        ∘ᵥ T₃ ▷ associator.to                                                          ≈⟨ sym-assoc₂ ⟩
      (actionˡ₂ ◁ F₁ ∘ᵥ (actionʳ₂ ◁ T₂ ◁ F₁ ∘ᵥ associator.to ◁ F₁) ∘ᵥ associator.to)
        ∘ᵥ T₃ ▷ associator.to                                                          ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      ((actionˡ₂ ◁ F₁ ∘ᵥ actionʳ₂ ◁ T₂ ◁ F₁ ∘ᵥ associator.to ◁ F₁) ∘ᵥ associator.to)
        ∘ᵥ T₃ ▷ associator.to                                                          ≈⟨ ((refl⟩∘⟨ ∘ᵥ-distr-◁) ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((actionˡ₂ ◁ F₁ ∘ᵥ (actionʳ₂ ◁ T₂ ∘ᵥ associator.to) ◁ F₁) ∘ᵥ associator.to)
        ∘ᵥ T₃ ▷ associator.to                                                          ≈⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩∘⟨refl ⟩
      ((actionˡ₂ ∘ᵥ actionʳ₂ ◁ T₂ ∘ᵥ associator.to) ◁ F₁ ∘ᵥ associator.to)
        ∘ᵥ T₃ ▷ associator.to                                                          ≈⟨ ◁-resp-≈ action-sym-assoc₂ ⟩∘⟨refl ⟩∘⟨refl ⟩
      ((actionʳ₂ ∘ᵥ (T₃ ▷ actionˡ₂)) ◁ F₁ ∘ᵥ associator.to) ∘ᵥ T₃ ▷ associator.to      ≈⟨ ⟺ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩∘⟨refl ⟩
      ((actionʳ₂ ◁ F₁ ∘ᵥ (T₃ ▷ actionˡ₂) ◁ F₁) ∘ᵥ associator.to) ∘ᵥ T₃ ▷ associator.to ≈⟨ (assoc₂ ⟩∘⟨refl) ⟩
      (actionʳ₂ ◁ F₁ ∘ᵥ (T₃ ▷ actionˡ₂) ◁ F₁ ∘ᵥ associator.to) ∘ᵥ T₃ ▷ associator.to   ≈⟨ (refl⟩∘⟨ ⟺ α⇐-▷-◁) ⟩∘⟨refl ⟩
      (actionʳ₂ ◁ F₁ ∘ᵥ associator.to ∘ᵥ T₃ ▷ (actionˡ₂ ◁ F₁)) ∘ᵥ T₃ ▷ associator.to   ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ₂ ◁ F₁ ∘ᵥ associator.to) ∘ᵥ T₃ ▷ (actionˡ₂ ◁ F₁)) ∘ᵥ T₃ ▷ associator.to ≈⟨ assoc₂ ⟩
      (actionʳ₂ ◁ F₁ ∘ᵥ associator.to) ∘ᵥ T₃ ▷ (actionˡ₂ ◁ F₁) ∘ᵥ T₃ ▷ associator.to   ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
      actionʳ₂◁F₁ ∘ᵥ T₃ ▷ (act-to-the-right)                             ∎
        where
          open hom.HomReasoning
          open hom.Equiv
  -- end abstract --

  -- right-action --
  actionʳ : T₃ ∘₁ F-⊗ ⇒₂ F-⊗
  actionʳ = ⇒MapBetweenCoeq actionʳ₂◁T₂∘₁F₁ actionʳ₂◁F₁ sq₁ sq₂ T₃∘FCoequalizer CoeqBimods
    where
      open CoeqProperties (hom C₁ C₃)

  abstract
    -- the right-action fits into the following commutaitve square --
    actionʳSq : CommutativeSquare (actionʳ₂◁F₁) (Coequalizer.arr T₃∘FCoequalizer) (Coequalizer.arr CoeqBimods) (actionʳ)
    actionʳSq = ⇒MapBetweenCoeqSq actionʳ₂◁T₂∘₁F₁ actionʳ₂◁F₁ sq₁ sq₂ T₃∘FCoequalizer CoeqBimods
      where
        open CoeqProperties (hom C₁ C₃)
  -- end abstract --

module Associativity where
  open Left-Action using (actionˡ-⊗; actionˡSq; actionˡ-∘)
  open Right-Action using (actionʳ; actionʳSq; actionʳ₂◁F₁; T₃∘FCoequalizer)

  -- we need that T₃∘(F∘T₁) is a coequalizer --
  T₃∘[F∘T₁]Coequalizer : Coequalizer (hom C₁ C₃) (T₃ ▷ ((act-to-the-left) ◁ T₁))  (T₃ ▷ ((act-to-the-right) ◁ T₁))
  T₃∘[F∘T₁]Coequalizer = T₃ ▷-coeq (CoeqBimods coeq-◁ T₁)

  -- we need that (T₃∘F)∘T₁ is a coequalizer --
  [T₃∘F]∘T₁Coequalizer : Coequalizer (hom C₁ C₃) ((T₃ ▷ (act-to-the-left)) ◁ T₁) ((T₃ ▷ (act-to-the-right)) ◁ T₁)
  [T₃∘F]∘T₁Coequalizer = T₃∘FCoequalizer coeq-◁ T₁

  abstract
    assoc-pentagon : actionʳ₂◁F₁ ∘ᵥ T₃ ▷ actionˡ-∘ ∘ᵥ associator.from ≈ actionˡ-∘ ∘ᵥ actionʳ₂◁F₁ ◁ T₁
    assoc-pentagon = begin
      actionʳ₂◁F₁ ∘ᵥ T₃ ▷ actionˡ-∘ ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ (⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl) ⟩
      actionʳ₂◁F₁ ∘ᵥ (T₃ ▷ F₂ ▷ actionˡ₁ ∘ᵥ T₃ ▷ associator.from) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ associator.to ∘ᵥ (T₃ ▷ F₂ ▷ actionˡ₁ ∘ᵥ T₃ ▷ associator.from) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ (associator.to ∘ᵥ (T₃ ▷ F₂ ▷ actionˡ₁ ∘ᵥ T₃ ▷ associator.from)) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ ((associator.to ∘ᵥ T₃ ▷ F₂ ▷ actionˡ₁) ∘ᵥ T₃ ▷ associator.from) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ (associator.to ∘ᵥ T₃ ▷ F₂ ▷ actionˡ₁) ∘ᵥ T₃ ▷ associator.from ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ α⇐-▷-∘₁ ⟩∘⟨refl ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ ((T₃ ∘₁ F₂) ▷ actionˡ₁ ∘ᵥ associator.to) ∘ᵥ T₃ ▷ associator.from ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩
      (actionʳ₂ ◁ F₁ ∘ᵥ ((T₃ ∘₁ F₂) ▷ actionˡ₁ ∘ᵥ associator.to)) ∘ᵥ T₃ ▷ associator.from ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ₂ ◁ F₁ ∘ᵥ (T₃ ∘₁ F₂) ▷ actionˡ₁) ∘ᵥ associator.to) ∘ᵥ T₃ ▷ associator.from ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      (actionʳ₂ ◁ F₁ ∘ᵥ (T₃ ∘₁ F₂) ▷ actionˡ₁) ∘ᵥ associator.to ∘ᵥ T₃ ▷ associator.from ∘ᵥ associator.from ≈⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
      (F₂ ▷ actionˡ₁ ∘ᵥ actionʳ₂ ◁ (F₁ ∘₁ T₁)) ∘ᵥ associator.to ∘ᵥ T₃ ▷ associator.from ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ pentagon-conjugate₁ ⟩
      (F₂ ▷ actionˡ₁ ∘ᵥ actionʳ₂ ◁ (F₁ ∘₁ T₁)) ∘ᵥ associator.from ∘ᵥ associator.to ◁ T₁ ≈⟨ assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ actionʳ₂ ◁ (F₁ ∘₁ T₁) ∘ᵥ associator.from ∘ᵥ associator.to ◁ T₁ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ (actionʳ₂ ◁ (F₁ ∘₁ T₁) ∘ᵥ associator.from) ∘ᵥ associator.to ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ α⇒-◁-∘₁ ⟩∘⟨refl ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ (associator.from ∘ᵥ actionʳ₂ ◁ F₁ ◁ T₁) ∘ᵥ associator.to ◁ T₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ associator.from ∘ᵥ actionʳ₂ ◁ F₁ ◁ T₁ ∘ᵥ associator.to ◁ T₁ ≈⟨ sym-assoc₂ ⟩
      (F₂ ▷ actionˡ₁ ∘ᵥ associator.from) ∘ᵥ actionʳ₂ ◁ F₁ ◁ T₁ ∘ᵥ associator.to ◁ T₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-∘ ∘ᵥ actionʳ₂◁F₁ ◁ T₁ ∎
      where
        open hom.HomReasoning

    assoc∘arr : (actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ associator.from) ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer)
                ≈ (actionˡ-⊗ ∘ᵥ (actionʳ ◁ T₁)) ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer)
    assoc∘arr = begin
      (actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ associator.from) ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer) ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ associator.from) ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer) ≈⟨ assoc₂ ⟩
      (actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ associator.from ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer) ≈⟨ refl⟩∘⟨ α⇒-▷-◁ ⟩
      (actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ Coequalizer.arr T₃∘[F∘T₁]Coequalizer ∘ᵥ associator.from  ≈⟨ sym-assoc₂ ⟩
      ((actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ Coequalizer.arr T₃∘[F∘T₁]Coequalizer) ∘ᵥ associator.from  ≈⟨ assoc₂ ⟩∘⟨refl ⟩
      (actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ Coequalizer.arr T₃∘[F∘T₁]Coequalizer) ∘ᵥ associator.from  ≈⟨ (refl⟩∘⟨ ∘ᵥ-distr-▷) ⟩∘⟨refl ⟩
      (actionʳ ∘ᵥ T₃ ▷ (actionˡ-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods coeq-◁ T₁))) ∘ᵥ associator.from  ≈⟨ (refl⟩∘⟨ ▷-resp-≈ (⟺ actionˡSq)) ⟩∘⟨refl ⟩
      (actionʳ ∘ᵥ T₃ ▷ (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘)) ∘ᵥ associator.from  ≈⟨ (refl⟩∘⟨(⟺ ∘ᵥ-distr-▷)) ⟩∘⟨refl ⟩
      (actionʳ ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ∘ᵥ T₃ ▷ actionˡ-∘) ∘ᵥ associator.from  ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ ∘ᵥ Coequalizer.arr T₃∘FCoequalizer) ∘ᵥ T₃ ▷ actionˡ-∘) ∘ᵥ associator.from  ≈⟨ (⟺ actionʳSq) ⟩∘⟨refl ⟩∘⟨refl ⟩
      ((Coequalizer.arr CoeqBimods ∘ᵥ actionʳ₂◁F₁) ∘ᵥ T₃ ▷ actionˡ-∘) ∘ᵥ associator.from  ≈⟨ assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ₂◁F₁) ∘ᵥ T₃ ▷ actionˡ-∘ ∘ᵥ associator.from  ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ₂◁F₁ ∘ᵥ T₃ ▷ actionˡ-∘ ∘ᵥ associator.from  ≈⟨ refl⟩∘⟨ assoc-pentagon ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ actionʳ₂◁F₁ ◁ T₁  ≈⟨ sym-assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ actionʳ₂◁F₁ ◁ T₁  ≈⟨ actionˡSq ⟩∘⟨refl ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods coeq-◁ T₁)) ∘ᵥ actionʳ₂◁F₁ ◁ T₁  ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods coeq-◁ T₁) ∘ᵥ actionʳ₂◁F₁ ◁ T₁  ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ₂◁F₁) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ actionʳSq ⟩
      actionˡ-⊗ ∘ᵥ (actionʳ ∘ᵥ Coequalizer.arr T₃∘FCoequalizer) ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ actionʳ ◁ T₁ ∘ᵥ Coequalizer.arr [T₃∘F]∘T₁Coequalizer ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionʳ ◁ T₁)) ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer) ∎
      where
        open hom.HomReasoning

    assoc : actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ associator.from ≈ actionˡ-⊗ ∘ᵥ (actionʳ ◁ T₁)
    assoc = Coequalizer⇒Epi (hom C₁ C₃) [T₃∘F]∘T₁Coequalizer
                            (actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ associator.from)
                            (actionˡ-⊗ ∘ᵥ (actionʳ ◁ T₁))
                            assoc∘arr

    assoc-var : (actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ associator.from ≈ actionˡ-⊗ ∘ᵥ (actionʳ ◁ T₁)
    assoc-var = begin
      (actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ associator.from ≈⟨ assoc ⟩
      actionˡ-⊗ ∘ᵥ (actionʳ ◁ T₁) ∎
      where
        open hom.HomReasoning

    sym-assoc : actionˡ-⊗ ∘ᵥ (actionʳ ◁ T₁) ∘ᵥ associator.to ≈ actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗)
    sym-assoc = begin
      actionˡ-⊗ ∘ᵥ (actionʳ ◁ T₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionʳ ◁ T₁)) ∘ᵥ associator.to ≈⟨ ⟺ (switch-fromtoʳ associator assoc-var) ⟩
      actionʳ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∎
      where
        open hom.HomReasoning
        open import Categories.Morphism.Reasoning.Iso (hom C₁ C₃)

  -- end abstarct --

  --  we need that (F∘T₁)∘T₁ is a coequalizer --
  [F∘T₁]∘T₁Coequalizer : Coequalizer (hom C₁ C₃) (((act-to-the-left) ◁ T₁) ◁ T₁) (((act-to-the-right) ◁ T₁) ◁ T₁)
  [F∘T₁]∘T₁Coequalizer = (CoeqBimods coeq-◁ T₁) coeq-◁ T₁

  abstract
    assoc-actionˡ-pentagon : actionˡ-∘ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈ actionˡ-∘ ∘ᵥ actionˡ-∘ ◁ T₁
    assoc-actionˡ-pentagon = begin
      actionˡ-∘ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ associator.from ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ (associator.from ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ α⇒-▷-∘₁ ⟩∘⟨refl ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ (F₂ ▷ F₁ ▷ μ₁ ∘ᵥ associator.from) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ F₁ ▷ μ₁ ∘ᵥ associator.from ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ pentagon ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ F₁ ▷ μ₁ ∘ᵥ F₂ ▷ associator.from ∘ᵥ associator.from ∘ᵥ associator.from ◁ T₁ ≈⟨ sym-assoc₂ ⟩
      (F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ F₁ ▷ μ₁) ∘ᵥ F₂ ▷ associator.from ∘ᵥ associator.from ∘ᵥ associator.from ◁ T₁ ≈⟨ sym-assoc₂ ⟩
      ((F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ F₁ ▷ μ₁) ∘ᵥ F₂ ▷ associator.from) ∘ᵥ associator.from ∘ᵥ associator.from ◁ T₁ ≈⟨ assoc₂ ⟩∘⟨refl ⟩
      (F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ F₁ ▷ μ₁ ∘ᵥ F₂ ▷ associator.from) ∘ᵥ associator.from ∘ᵥ associator.from ◁ T₁ ≈⟨ (refl⟩∘⟨ ∘ᵥ-distr-▷) ⟩∘⟨refl ⟩
      (F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ (F₁ ▷ μ₁ ∘ᵥ associator.from)) ∘ᵥ associator.from ∘ᵥ associator.from ◁ T₁ ≈⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
      F₂ ▷ (actionˡ₁ ∘ᵥ F₁ ▷ μ₁ ∘ᵥ associator.from) ∘ᵥ associator.from ∘ᵥ associator.from ◁ T₁ ≈⟨ ▷-resp-≈ assoc-actionˡ₁ ⟩∘⟨refl ⟩
      F₂ ▷ (actionˡ₁ ∘ᵥ actionˡ₁ ◁ T₁) ∘ᵥ associator.from ∘ᵥ associator.from ◁ T₁ ≈⟨ ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
      (F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ (actionˡ₁ ◁ T₁)) ∘ᵥ associator.from ∘ᵥ associator.from ◁ T₁ ≈⟨ assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ (actionˡ₁ ◁ T₁) ∘ᵥ associator.from ∘ᵥ associator.from ◁ T₁ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ (F₂ ▷ (actionˡ₁ ◁ T₁) ∘ᵥ associator.from) ∘ᵥ associator.from ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ α⇒-▷-◁ ⟩∘⟨refl ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ (associator.from ∘ᵥ (F₂ ▷ actionˡ₁) ◁ T₁) ∘ᵥ associator.from ◁ T₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ associator.from ∘ᵥ (F₂ ▷ actionˡ₁) ◁ T₁ ∘ᵥ associator.from ◁ T₁ ≈⟨ sym-assoc₂ ⟩
      (F₂ ▷ actionˡ₁ ∘ᵥ associator.from) ∘ᵥ (F₂ ▷ actionˡ₁) ◁ T₁ ∘ᵥ associator.from ◁ T₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-∘ ∘ᵥ actionˡ-∘ ◁ T₁ ∎
      where
        open hom.HomReasoning

    assoc-actionˡ∘arr : (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ associator.from) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer
                        ≈ (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁)) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer
    assoc-actionˡ∘arr = begin
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ associator.from) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      ((actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)) ∘ᵥ associator.from) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer ≈⟨ assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)) ∘ᵥ associator.from ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer ≈⟨ refl⟩∘⟨ α⇒-◁-∘₁ ⟩
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)) ∘ᵥ Coequalizer.arr CoeqBimods ◁ (T₁ ∘₁ T₁) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ Coequalizer.arr CoeqBimods ◁ (T₁ ∘₁ T₁) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ ((F-⊗ ▷ μ₁) ∘ᵥ Coequalizer.arr CoeqBimods ◁ (T₁ ∘₁ T₁)) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁) ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ ⟺ actionˡSq ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ assoc-actionˡ-pentagon ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ actionˡ-∘ ◁ T₁ ≈⟨ sym-assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ actionˡ-∘ ◁ T₁ ≈⟨ actionˡSq ⟩∘⟨refl ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁) ∘ᵥ actionˡ-∘ ◁ T₁ ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁ ∘ᵥ actionˡ-∘ ◁ T₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ actionˡSq ⟩
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁) ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁)) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer ∎
      where
        open hom.HomReasoning

    assoc-actionˡ : actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ associator.from ≈ actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁)
    assoc-actionˡ = Coequalizer⇒Epi ((hom C₁ C₃)) [F∘T₁]∘T₁Coequalizer
                                    (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ associator.from)
                                    (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁))
                                    assoc-actionˡ∘arr

    assoc-actionˡ-var : (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)) ∘ᵥ associator.from ≈ actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁)
    assoc-actionˡ-var = begin
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ associator.from ≈⟨ assoc-actionˡ ⟩
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁) ∎
      where
        open hom.HomReasoning

    sym-assoc-actionˡ : actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁) ∘ᵥ associator.to ≈ actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)
    sym-assoc-actionˡ = begin
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁)) ∘ᵥ associator.to ≈⟨ ⟺ (switch-fromtoʳ associator assoc-actionˡ-var) ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∎
      where
        open hom.HomReasoning
        open import Categories.Morphism.Reasoning.Iso (hom C₁ C₃)
  -- end abstract --

  --  we need that T₃∘(T₃∘F) is a coequalizer --
  T₃∘[T₃∘F]Coequalizer : Coequalizer (hom C₁ C₃) (T₃ ▷ T₃ ▷ (act-to-the-left)) (T₃ ▷ T₃ ▷ (act-to-the-right))
  T₃∘[T₃∘F]Coequalizer = T₃ ▷-coeq T₃∘FCoequalizer

  abstract
    assoc-actionʳ-pentagon : actionʳ₂◁F₁ ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈ actionʳ₂◁F₁ ∘ᵥ T₃ ▷ actionʳ₂◁F₁
    assoc-actionʳ-pentagon = begin
      actionʳ₂◁F₁ ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ associator.to ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ (associator.to ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁)) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ α⇐-◁-∘₁ ⟩∘⟨refl ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ (μ₃ ◁ F₂ ◁ F₁ ∘ᵥ associator.to) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ μ₃ ◁ F₂ ◁ F₁ ∘ᵥ associator.to ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ pentagon-inv ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ μ₃ ◁ F₂ ◁ F₁ ∘ᵥ (associator.to ◁ F₁ ∘ᵥ associator.to) ∘ᵥ T₃ ▷ associator.to ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ μ₃ ◁ F₂ ◁ F₁ ∘ᵥ associator.to ◁ F₁ ∘ᵥ associator.to ∘ᵥ T₃ ▷ associator.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ (μ₃ ◁ F₂ ◁ F₁ ∘ᵥ associator.to ◁ F₁) ∘ᵥ associator.to ∘ᵥ T₃ ▷ associator.to ≈⟨ sym-assoc₂ ⟩
      (actionʳ₂ ◁ F₁ ∘ᵥ μ₃ ◁ F₂ ◁ F₁ ∘ᵥ associator.to ◁ F₁) ∘ᵥ associator.to ∘ᵥ T₃ ▷ associator.to ≈⟨ (refl⟩∘⟨ ∘ᵥ-distr-◁) ⟩∘⟨refl ⟩
      (actionʳ₂ ◁ F₁ ∘ᵥ (μ₃ ◁ F₂ ∘ᵥ associator.to) ◁ F₁) ∘ᵥ associator.to ∘ᵥ T₃ ▷ associator.to ≈⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩
      (actionʳ₂ ∘ᵥ μ₃ ◁ F₂ ∘ᵥ associator.to) ◁ F₁ ∘ᵥ associator.to ∘ᵥ T₃ ▷ associator.to ≈⟨ ◁-resp-≈ assoc-actionʳ₂ ⟩∘⟨refl ⟩
      (actionʳ₂ ∘ᵥ T₃ ▷ actionʳ₂) ◁ F₁ ∘ᵥ associator.to ∘ᵥ T₃ ▷ associator.to ≈⟨ ⟺ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩
      (actionʳ₂ ◁ F₁ ∘ᵥ (T₃ ▷ actionʳ₂) ◁ F₁) ∘ᵥ associator.to ∘ᵥ T₃ ▷ associator.to ≈⟨ assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ (T₃ ▷ actionʳ₂) ◁ F₁ ∘ᵥ associator.to ∘ᵥ T₃ ▷ associator.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ ((T₃ ▷ actionʳ₂) ◁ F₁ ∘ᵥ associator.to) ∘ᵥ T₃ ▷ associator.to ≈⟨ refl⟩∘⟨ ⟺ α⇐-▷-◁ ⟩∘⟨refl ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ (associator.to ∘ᵥ T₃ ▷ (actionʳ₂ ◁ F₁)) ∘ᵥ T₃ ▷ associator.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ associator.to ∘ᵥ T₃ ▷ (actionʳ₂ ◁ F₁) ∘ᵥ T₃ ▷ associator.to ≈⟨ sym-assoc₂ ⟩
      actionʳ₂◁F₁ ∘ᵥ T₃ ▷ (actionʳ₂ ◁ F₁) ∘ᵥ T₃ ▷ associator.to ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
      actionʳ₂◁F₁ ∘ᵥ T₃ ▷ actionʳ₂◁F₁ ∎
      where
        open hom.HomReasoning

    assoc-actionʳ∘arr : (actionʳ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ associator.to) ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer
                        ≈ (actionʳ ∘ᵥ T₃ ▷ actionʳ) ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer
    assoc-actionʳ∘arr = begin
      (actionʳ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ associator.to) ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ ∘ᵥ μ₃ ◁ F-⊗) ∘ᵥ associator.to) ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer ≈⟨ assoc₂ ⟩
      (actionʳ ∘ᵥ μ₃ ◁ F-⊗) ∘ᵥ associator.to ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer ≈⟨ refl⟩∘⟨ α⇐-▷-∘₁ ⟩
      (actionʳ ∘ᵥ μ₃ ◁ F-⊗) ∘ᵥ (T₃ ∘₁ T₃) ▷ Coequalizer.arr CoeqBimods ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
      actionʳ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ (T₃ ∘₁ T₃) ▷ Coequalizer.arr CoeqBimods ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionʳ ∘ᵥ (μ₃ ◁ F-⊗ ∘ᵥ (T₃ ∘₁ T₃) ▷ Coequalizer.arr CoeqBimods) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionʳ ∘ᵥ (T₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁)) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
      (actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ ⟺ actionʳSq ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ₂◁F₁) ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ₂◁F₁ ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ assoc-actionʳ-pentagon ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ₂◁F₁ ∘ᵥ T₃ ▷ actionʳ₂◁F₁ ≈⟨ sym-assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ₂◁F₁) ∘ᵥ T₃ ▷ actionʳ₂◁F₁ ≈⟨ actionʳSq ⟩∘⟨refl ⟩
      (actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ T₃ ▷ actionʳ₂◁F₁ ≈⟨ assoc₂ ⟩
      actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ T₃ ▷ actionʳ₂◁F₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
      actionʳ ∘ᵥ T₃ ▷ (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ₂◁F₁) ≈⟨ refl⟩∘⟨ ▷-resp-≈ actionʳSq ⟩
      actionʳ ∘ᵥ T₃ ▷ (actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods) ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩
      actionʳ ∘ᵥ T₃ ▷ actionʳ ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer ≈⟨ sym-assoc₂ ⟩
      (actionʳ ∘ᵥ T₃ ▷ actionʳ) ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer ∎
      where
        open hom.HomReasoning

    assoc-actionʳ : actionʳ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ associator.to ≈ actionʳ ∘ᵥ T₃ ▷ actionʳ
    assoc-actionʳ = Coequalizer⇒Epi (hom C₁ C₃) T₃∘[T₃∘F]Coequalizer
                                    (actionʳ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ associator.to)
                                    (actionʳ ∘ᵥ T₃ ▷ actionʳ)
                                    assoc-actionʳ∘arr

    assoc-actionʳ-var : (actionʳ ∘ᵥ μ₃ ◁ F-⊗) ∘ᵥ associator.to ≈ actionʳ ∘ᵥ T₃ ▷ actionʳ
    assoc-actionʳ-var = begin
      (actionʳ ∘ᵥ μ₃ ◁ F-⊗) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
      actionʳ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ associator.to ≈⟨ assoc-actionʳ ⟩
      actionʳ ∘ᵥ T₃ ▷ actionʳ ∎
      where
        open hom.HomReasoning

    sym-assoc-actionʳ : actionʳ ∘ᵥ T₃ ▷ actionʳ ∘ᵥ associator.from ≈ actionʳ ∘ᵥ μ₃ ◁ F-⊗
    sym-assoc-actionʳ = begin
      actionʳ ∘ᵥ T₃ ▷ actionʳ ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩
      (actionʳ ∘ᵥ T₃ ▷ actionʳ) ∘ᵥ associator.from ≈⟨ ⟺ (switch-tofromʳ associator assoc-actionʳ-var) ⟩
      actionʳ ∘ᵥ μ₃ ◁ F-⊗ ∎
      where
        open hom.HomReasoning
        open import Categories.Morphism.Reasoning.Iso (hom C₁ C₃)
  -- end abstract --

module Identity where
  open Left-Action using (actionˡ-⊗; actionˡSq; actionˡ-∘)
  open Right-Action using (actionʳ; actionʳSq; actionʳ₂◁F₁; T₃∘FCoequalizer)

  abstract
    identityˡ-triangle : actionˡ-∘ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈ id₂
    identityˡ-triangle = begin
      actionˡ-∘ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ associator.from ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ (associator.from ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁) ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ α⇒-▷-∘₁ ⟩∘⟨refl ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ (F₂ ▷ F₁ ▷ η₁ ∘ᵥ associator.from) ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ F₁ ▷ η₁ ∘ᵥ associator.from ∘ᵥ unitorʳ.to ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ ⟺ unitorʳ-coherence-var₂) ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ F₁ ▷ η₁ ∘ᵥ F₂ ▷ unitorʳ.to ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
      F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ (F₁ ▷ η₁ ∘ᵥ unitorʳ.to) ≈⟨ ∘ᵥ-distr-▷ ⟩
      F₂ ▷ (actionˡ₁ ∘ᵥ F₁ ▷ η₁ ∘ᵥ unitorʳ.to) ≈⟨ ▷-resp-≈ identityˡ₁ ⟩
      F₂ ▷ id₂ ≈⟨ ▷id₂ ⟩
      id₂ ∎
      where
        open hom.HomReasoning

    identityˡ∘arr : (actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈ id₂ ∘ᵥ Coequalizer.arr CoeqBimods
    identityˡ∘arr = begin
      (actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ◁-∘ᵥ-ρ⇐ ⟩
      actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ Coequalizer.arr CoeqBimods ◁ id₁ ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ η₁ ∘ᵥ Coequalizer.arr CoeqBimods ◁ id₁) ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁) ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁) ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ ⟺ actionˡSq ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ identityˡ-triangle ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ id₂ ≈⟨ identity₂ʳ ⟩
      Coequalizer.arr CoeqBimods ≈⟨ ⟺ identity₂ˡ ⟩
      id₂ ∘ᵥ Coequalizer.arr CoeqBimods ∎
      where
        open hom.HomReasoning

    identityˡ : actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to ≈ id₂
    identityˡ = Coequalizer⇒Epi (hom C₁ C₃) CoeqBimods (actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to) id₂ identityˡ∘arr


    identityʳ-triangle : actionʳ₂◁F₁ ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈ id₂
    identityʳ-triangle = begin
      actionʳ₂◁F₁ ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ associator.to ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ (associator.to ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁)) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ α⇐-◁-∘₁ ⟩∘⟨refl ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ (η₃ ◁ F₂ ◁ F₁ ∘ᵥ associator.to) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ η₃ ◁ F₂ ◁ F₁ ∘ᵥ associator.to ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ unitorˡ-coherence-inv ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ η₃ ◁ F₂ ◁ F₁ ∘ᵥ unitorˡ.to ◁ F₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionʳ₂ ◁ F₁ ∘ᵥ (η₃ ◁ F₂ ∘ᵥ unitorˡ.to) ◁ F₁ ≈⟨ ∘ᵥ-distr-◁ ⟩
      (actionʳ₂ ∘ᵥ η₃ ◁ F₂ ∘ᵥ unitorˡ.to) ◁ F₁ ≈⟨ ◁-resp-≈ identityʳ₂ ⟩
      id₂ ◁ F₁ ≈⟨ id₂◁ ⟩
      id₂ ∎
      where
        open hom.HomReasoning

    identityʳ∘arr : (actionʳ ∘ᵥ η₃ ◁ F-⊗ ∘ᵥ unitorˡ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈ id₂ ∘ᵥ Coequalizer.arr CoeqBimods
    identityʳ∘arr = begin
      (actionʳ ∘ᵥ η₃ ◁ F-⊗ ∘ᵥ unitorˡ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ assoc₂ ⟩
      actionʳ ∘ᵥ (η₃ ◁ F-⊗ ∘ᵥ unitorˡ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ ∘ᵥ η₃ ◁ F-⊗ ∘ᵥ unitorˡ.to ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ▷-∘ᵥ-λ⇐ ⟩
      actionʳ ∘ᵥ η₃ ◁ F-⊗ ∘ᵥ id₁ ▷ Coequalizer.arr CoeqBimods ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionʳ ∘ᵥ (η₃ ◁ F-⊗ ∘ᵥ id₁ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionʳ ∘ᵥ (T₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁)) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ sym-assoc₂ ⟩
      (actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ ⟺ actionʳSq ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ₂◁F₁) ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ₂◁F₁ ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ identityʳ-triangle ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ id₂ ≈⟨ identity₂ʳ ⟩
      Coequalizer.arr CoeqBimods ≈⟨ ⟺ identity₂ˡ ⟩
      id₂ ∘ᵥ Coequalizer.arr CoeqBimods ∎
      where
        open hom.HomReasoning

    identityʳ : actionʳ ∘ᵥ (η₃ ◁ F-⊗) ∘ᵥ unitorˡ.to ≈ id₂
    identityʳ = Coequalizer⇒Epi (hom C₁ C₃) CoeqBimods (actionʳ ∘ᵥ (η₃ ◁ F-⊗) ∘ᵥ unitorˡ.to) id₂ identityʳ∘arr
  -- end abstract --

B₂⊗B₁ : Bimodule M₁ M₃
B₂⊗B₁ = record
  { F = F-⊗
  ; actionˡ = Left-Action.actionˡ-⊗ --: F ∘₁ T₁ ⇒₂ F  
  ; actionʳ = Right-Action.actionʳ --: T₂ ∘₁ F ⇒₂ F 
  ; assoc = Associativity.assoc    -- : actionʳ ∘ᵥ (T₂ ▷ actionˡ) ∘ᵥ associator.from ≈ actionˡ ∘ᵥ (actionʳ ◁ T₁)
  ; sym-assoc = Associativity.sym-assoc --: actionˡ ∘ᵥ (actionʳ ◁ T₁)∘ᵥ associator.to ≈ actionʳ ∘ᵥ (T₂ ▷ actionˡ)
  ; assoc-actionˡ = Associativity.assoc-actionˡ     --: actionˡ ∘ᵥ (F ▷ μ₁) ∘ᵥ associator.from ≈ actionˡ ∘ᵥ (actionˡ ◁ T₁)
  ; sym-assoc-actionˡ = Associativity.sym-assoc-actionˡ --: actionˡ ∘ᵥ (actionˡ ◁ T₁) ∘ᵥ associator.to ≈ actionˡ ∘ᵥ (F ▷ μ₁)
  ; assoc-actionʳ = Associativity.assoc-actionʳ     --: actionʳ ∘ᵥ (μ₂ ◁ F) ∘ᵥ associator.to ≈ actionʳ ∘ᵥ (T₂ ▷ actionʳ)
  ; sym-assoc-actionʳ = Associativity.sym-assoc-actionʳ --: actionʳ ∘ᵥ (T₂ ▷ actionʳ) ∘ᵥ associator.from ≈ actionʳ ∘ᵥ (μ₂ ◁ F)
  ; identityˡ = Identity.identityˡ --: actionˡ ∘ᵥ (F ▷ η₁) ∘ᵥ unitorʳ.to ≈ id₂
  ; identityʳ = Identity.identityʳ --: actionʳ ∘ᵥ (η₂ ◁ F) ∘ᵥ unitorˡ.to ≈ id₂
  }
