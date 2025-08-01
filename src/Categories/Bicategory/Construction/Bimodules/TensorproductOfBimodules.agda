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

private
  module Bimodules₁ M₁ M₂ = Category (Bimodules₁ M₁ M₂)

open LocalCoequalizers localCoeq
open ComposeWithLocalCoequalizer 𝒞 localCoeq using (_coeq-◁_; _▷-coeq_)

private
  module homCat {X} {Y} where
    open import Categories.Diagram.Coequalizer (hom X Y) public using (Coequalizer; Coequalizer⇒Epi)
    open import Categories.Diagram.Coequalizer.Properties (hom X Y) public
      using (⇒MapBetweenCoeq; ⇒MapBetweenCoeqSq)

open homCat

open Monad
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

abstract
  -- to costruct the tensorproduct of bimodules the following coequalizer is formed --
  -- to speed-up type-checking we hide the definition of this coequalizer under an abstract clause --
  -- for all foreseeable purposes, the particular choice of coequalizer will not matter --
  CoeqBimods : Coequalizer (act-to-the-left) (act-to-the-right)
  CoeqBimods = local-coequalizers (act-to-the-left) (act-to-the-right)
  
-- The underlying object of that coequalizer is the underlying 1-cell of the bimodule B₂⊗B₁ --
F-⊗ : C₁ ⇒₁ C₃
F-⊗ = Coequalizer.obj CoeqBimods


module Left-Action where

  {-
                                 act-to-the-left ◁ T M₁
    (F B₂ ∘ T M₂ ∘ F B₁) ∘ T M₁ ========================> (F B₂ ∘ F B₁) ∘ T M₁ ---> F ∘ T M₁      ::     CoeqBimods coeq-◁ T M₁
             |                   act-to-the-right ◁ T M₁            |                  .
             |                                                      |                  .
         actionˡ-∘-∘                                             actionˡ-∘          actionˡ-⊗
             |                                                      |                  .
             v                      act-to-the-left                 v                  v
    F B₂ ∘ T M₂ ∘ F B₁ ======================================> F B₂ ∘ F B₁ ----------> F          ::     CoeqBimods
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

  abstract    
    -- left-action --
    -- to speed-up type-checking we hide the definition of the left-action under an abstract clause --
    -- probably, no one ever wants to look into its defintion and instead only use the lemma actionˡSq-⊗ below --
    actionˡ-⊗ : F-⊗ ∘₁ T₁ ⇒₂ F-⊗
    actionˡ-⊗ = ⇒MapBetweenCoeq actionˡ-∘-∘ actionˡ-∘ sq₁ sq₂ (CoeqBimods coeq-◁ T₁) CoeqBimods

    -- the left-action fits into the following commutative square --
    actionˡSq-⊗ : CommutativeSquare (actionˡ-∘) (Coequalizer.arr (CoeqBimods coeq-◁ T₁)) (Coequalizer.arr CoeqBimods) (actionˡ-⊗)
    actionˡSq-⊗ = ⇒MapBetweenCoeqSq actionˡ-∘-∘ actionˡ-∘ sq₁ sq₂ (CoeqBimods coeq-◁ T₁) CoeqBimods
  -- end abstract --

module Right-Action where

  {-
                                 T M₃ ▷ act-to-the-left
    T M₃ ∘ (F B₂ ∘ T M₂ ∘ F B₁) ========================> T M₃ ∘ (F B₂ ∘ F B₁) ---> T M₃ ∘ F      ::     T M₃ ▷-coeq CoeqBimods
             |                   T M₃ ▷ act-to-the-right            |                  .
             |                                                      |                  .
         actionʳ-∘-∘                                             actionʳ-∘          actionʳ-⊗
             |                                                      |                  .
             v                      act-to-the-left                 v                  v
    F B₂ ∘ T M₂ ∘ F B₁ ======================================> F B₂ ∘ F B₁ ----------> F          ::     CoeqBimods
                                    act-to-the-right
  -}

  -- to define a map between the coequalizers T₃ ∘₁ F-⊗ ⇒₂ F-⊗ we define a map of diagrams --
  actionʳ-∘-∘ : T₃ ∘₁ F₂ ∘₁ T₂ ∘₁ F₁ ⇒₂  F₂ ∘₁ T₂ ∘₁ F₁
  actionʳ-∘-∘ = actionʳ₂ ◁ (T₂ ∘₁ F₁) ∘ᵥ associator.to

  actionʳ-∘ : T₃ ∘₁ F₂ ∘₁ F₁ ⇒₂  F₂ ∘₁ F₁
  actionʳ-∘ = actionʳ₂ ◁ F₁ ∘ᵥ associator.to

  -- for CommutativeSquare --
  open Definitions (hom C₁ C₃)

  -- to get a map of diagrams two squares have to commute --
  abstract
    sq₁ : CommutativeSquare (actionʳ-∘-∘) (T₃ ▷ act-to-the-left) (act-to-the-left) (actionʳ-∘)
    sq₁ = glue′ sq₁bottom sq₁top
      where
        open hom.HomReasoning
        open import Categories.Morphism.Reasoning.Core (hom C₁ C₃)
        sq₁top : CommutativeSquare (associator.to) (T₃ ▷ F₂ ▷ actionʳ₁) ((T₃ ∘₁ F₂) ▷ actionʳ₁) (associator.to)
        sq₁top = ⟺ α⇐-▷-∘₁
        sq₁bottom : CommutativeSquare (actionʳ₂ ◁ (T₂ ∘₁ F₁)) ((T₃ ∘₁ F₂) ▷ actionʳ₁) (F₂ ▷ actionʳ₁) (actionʳ₂ ◁ F₁)
        sq₁bottom = ◁-▷-exchg

    sq₂ : CommutativeSquare (actionʳ-∘-∘) (T₃ ▷ (act-to-the-right)) (act-to-the-right) (actionʳ-∘)
    sq₂ = begin
      (act-to-the-right) ∘ᵥ (actionʳ-∘-∘)                            ≈⟨ sym-assoc₂ ⟩
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
      actionʳ-∘ ∘ᵥ T₃ ▷ (act-to-the-right)                             ∎
        where
          open hom.HomReasoning
          open hom.Equiv
  -- end abstract --

  abstract
    -- right-action --
    -- to speed-up type-checking we hide the definition of the right-action under an abstract clause --
    -- probably, no one ever wants to look into its defintion and instead only use the lemma actionʳSq-⊗ below --
    actionʳ-⊗ : T₃ ∘₁ F-⊗ ⇒₂ F-⊗
    actionʳ-⊗ = ⇒MapBetweenCoeq actionʳ-∘-∘ actionʳ-∘ sq₁ sq₂ (T₃ ▷-coeq CoeqBimods) CoeqBimods

    -- the right-action fits into the following commutaitve square --
    actionʳSq-⊗ : CommutativeSquare (actionʳ-∘) (Coequalizer.arr (T₃ ▷-coeq CoeqBimods)) (Coequalizer.arr CoeqBimods) (actionʳ-⊗)
    actionʳSq-⊗ = ⇒MapBetweenCoeqSq actionʳ-∘-∘ actionʳ-∘ sq₁ sq₂ (T₃ ▷-coeq CoeqBimods) CoeqBimods
  -- end abstract --


-- Associativity and identity laws for bimodules each assert an equality of 2-cells.  --
-- To prove that the tensorproduct satisfies these equalities (assoc-⊗, sym-assoc-⊗, identityˡ-⊗ ,...) --
-- we show that the morphisms precomposed by a coequalizer arrow are equal (assoc-⊗-∘arr, sym-assoc-⊗-∘arr, identityˡ-⊗-∘arr,...). --
-- Finally, we use that coequalizer arrows are epis to cancell them --
-- In the proofs of assoc-⊗-∘arr, sym-assoc-⊗-∘arr, etc we use that a version of the associativity and identity laws hold for F B₂ ∘₁ F B₁. --
-- Note that F B₂ ∘₁ F B₁ is a bimodule under actionˡ-∘ and actionˡ-∘ (although we don't use that fact). --

module Associativity where
  open Left-Action using (actionˡ-⊗; actionˡSq-⊗; actionˡ-∘)
  open Right-Action using (actionʳ-⊗; actionʳSq-⊗; actionʳ-∘)

  abstract
    assoc-∘ : actionʳ-∘ ∘ᵥ T₃ ▷ actionˡ-∘ ∘ᵥ associator.from ≈ actionˡ-∘ ∘ᵥ actionʳ-∘ ◁ T₁
    assoc-∘ = begin
      actionʳ-∘ ∘ᵥ T₃ ▷ actionˡ-∘ ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ (⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl) ⟩
      actionʳ-∘ ∘ᵥ (T₃ ▷ F₂ ▷ actionˡ₁ ∘ᵥ T₃ ▷ associator.from) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
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
      actionˡ-∘ ∘ᵥ actionʳ-∘ ◁ T₁ ∎
      where
        open hom.HomReasoning

  abstract
    assoc-⊗-∘arr : (actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ associator.from) ∘ᵥ (Coequalizer.arr ((T₃ ▷-coeq CoeqBimods) coeq-◁ T₁))
                  ≈ (actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T₁)) ∘ᵥ (Coequalizer.arr ((T₃ ▷-coeq CoeqBimods) coeq-◁ T₁))
    assoc-⊗-∘arr = begin
      (actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ associator.from) ∘ᵥ (Coequalizer.arr ((T₃ ▷-coeq CoeqBimods) coeq-◁ T₁)) ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ associator.from) ∘ᵥ (Coequalizer.arr ((T₃ ▷-coeq CoeqBimods) coeq-◁ T₁)) ≈⟨ assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ associator.from ∘ᵥ (Coequalizer.arr ((T₃ ▷-coeq CoeqBimods) coeq-◁ T₁)) ≈⟨ refl⟩∘⟨ α⇒-▷-◁ ⟩
      (actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq (CoeqBimods coeq-◁ T₁)) ∘ᵥ associator.from  ≈⟨ sym-assoc₂ ⟩
      ((actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq (CoeqBimods coeq-◁ T₁))) ∘ᵥ associator.from  ≈⟨ assoc₂ ⟩∘⟨refl ⟩
      (actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq (CoeqBimods coeq-◁ T₁))) ∘ᵥ associator.from  ≈⟨ (refl⟩∘⟨ ∘ᵥ-distr-▷) ⟩∘⟨refl ⟩
      (actionʳ-⊗ ∘ᵥ T₃ ▷ (actionˡ-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods coeq-◁ T₁))) ∘ᵥ associator.from  ≈⟨ (refl⟩∘⟨ ▷-resp-≈ (⟺ actionˡSq-⊗)) ⟩∘⟨refl ⟩
      (actionʳ-⊗ ∘ᵥ T₃ ▷ (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘)) ∘ᵥ associator.from  ≈⟨ (refl⟩∘⟨(⟺ ∘ᵥ-distr-▷)) ⟩∘⟨refl ⟩
      (actionʳ-⊗ ∘ᵥ Coequalizer.arr (T₃ ▷-coeq CoeqBimods) ∘ᵥ T₃ ▷ actionˡ-∘) ∘ᵥ associator.from  ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ-⊗ ∘ᵥ Coequalizer.arr (T₃ ▷-coeq CoeqBimods)) ∘ᵥ T₃ ▷ actionˡ-∘) ∘ᵥ associator.from  ≈⟨ (⟺ actionʳSq-⊗) ⟩∘⟨refl ⟩∘⟨refl ⟩
      ((Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ∘ᵥ T₃ ▷ actionˡ-∘) ∘ᵥ associator.from  ≈⟨ assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ∘ᵥ T₃ ▷ actionˡ-∘ ∘ᵥ associator.from  ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘ ∘ᵥ T₃ ▷ actionˡ-∘ ∘ᵥ associator.from  ≈⟨ refl⟩∘⟨ assoc-∘ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ actionʳ-∘ ◁ T₁  ≈⟨ sym-assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ actionʳ-∘ ◁ T₁  ≈⟨ actionˡSq-⊗ ⟩∘⟨refl ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods coeq-◁ T₁)) ∘ᵥ actionʳ-∘ ◁ T₁  ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods coeq-◁ T₁) ∘ᵥ actionʳ-∘ ◁ T₁  ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ actionʳSq-⊗ ⟩
      actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ∘ᵥ Coequalizer.arr (T₃ ▷-coeq CoeqBimods)) ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ actionʳ-⊗ ◁ T₁ ∘ᵥ Coequalizer.arr ((T₃ ▷-coeq CoeqBimods) coeq-◁ T₁) ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T₁)) ∘ᵥ (Coequalizer.arr ((T₃ ▷-coeq CoeqBimods) coeq-◁ T₁)) ∎
      where
        open hom.HomReasoning

  abstract
    assoc-⊗ : actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ associator.from ≈ actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T₁)
    assoc-⊗ = Coequalizer⇒Epi ((T₃ ▷-coeq CoeqBimods) coeq-◁ T₁)
                              (actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ associator.from)
                              (actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T₁))
                              assoc-⊗-∘arr

  abstract
    assoc-⊗-var : (actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ associator.from ≈ actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T₁)
    assoc-⊗-var = begin
      (actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗)) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∘ᵥ associator.from ≈⟨ assoc-⊗ ⟩
      actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T₁) ∎
      where
        open hom.HomReasoning

  abstract
    sym-assoc-⊗ : actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T₁) ∘ᵥ associator.to ≈ actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗)
    sym-assoc-⊗ = begin
      actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T₁)) ∘ᵥ associator.to ≈⟨ ⟺ (switch-fromtoʳ associator assoc-⊗-var) ⟩
      actionʳ-⊗ ∘ᵥ (T₃ ▷ actionˡ-⊗) ∎
      where
        open hom.HomReasoning
        open import Categories.Morphism.Reasoning.Iso (hom C₁ C₃)

  abstract
    assoc-actionˡ-∘ : actionˡ-∘ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈ actionˡ-∘ ∘ᵥ actionˡ-∘ ◁ T₁
    assoc-actionˡ-∘ = begin
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

  abstract
    assoc-actionˡ-⊗-∘arr : (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ associator.from) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T₁) coeq-◁ T₁)
                        ≈ (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁)) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T₁) coeq-◁ T₁)
    assoc-actionˡ-⊗-∘arr = begin
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ associator.from) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T₁) coeq-◁ T₁) ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      ((actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)) ∘ᵥ associator.from) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T₁) coeq-◁ T₁) ≈⟨ assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)) ∘ᵥ associator.from ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T₁) coeq-◁ T₁) ≈⟨ refl⟩∘⟨ α⇒-◁-∘₁ ⟩
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)) ∘ᵥ Coequalizer.arr CoeqBimods ◁ (T₁ ∘₁ T₁) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ Coequalizer.arr CoeqBimods ◁ (T₁ ∘₁ T₁) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ ((F-⊗ ▷ μ₁) ∘ᵥ Coequalizer.arr CoeqBimods ◁ (T₁ ∘₁ T₁)) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁) ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ ⟺ actionˡSq-⊗ ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ assoc-actionˡ-∘ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ actionˡ-∘ ◁ T₁ ≈⟨ sym-assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ actionˡ-∘ ◁ T₁ ≈⟨ actionˡSq-⊗ ⟩∘⟨refl ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁) ∘ᵥ actionˡ-∘ ◁ T₁ ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁ ∘ᵥ actionˡ-∘ ◁ T₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ actionˡSq-⊗ ⟩
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁) ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T₁) coeq-◁ T₁) ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁)) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T₁) coeq-◁ T₁) ∎
      where
        open hom.HomReasoning

  abstract
    assoc-actionˡ-⊗ : actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ associator.from ≈ actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁)
    assoc-actionˡ-⊗ = Coequalizer⇒Epi ((CoeqBimods coeq-◁ T₁) coeq-◁ T₁)
                                      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ associator.from)
                                      (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁))
                                      assoc-actionˡ-⊗-∘arr

  abstract
    assoc-actionˡ-⊗-var : (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)) ∘ᵥ associator.from ≈ actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁)
    assoc-actionˡ-⊗-var = begin
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∘ᵥ associator.from ≈⟨ assoc-actionˡ-⊗ ⟩
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁) ∎
      where
        open hom.HomReasoning

  abstract
    sym-assoc-actionˡ-⊗ : actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁) ∘ᵥ associator.to ≈ actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁)
    sym-assoc-actionˡ-⊗ = begin
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T₁)) ∘ᵥ associator.to ≈⟨ ⟺ (switch-fromtoʳ associator assoc-actionˡ-⊗-var) ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ₁) ∎
      where
        open hom.HomReasoning
        open import Categories.Morphism.Reasoning.Iso (hom C₁ C₃)
  -- end abstract --

  abstract
    assoc-actionʳ-∘ : actionʳ-∘ ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈ actionʳ-∘ ∘ᵥ T₃ ▷ actionʳ-∘
    assoc-actionʳ-∘ = begin
      actionʳ-∘ ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
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
      actionʳ-∘ ∘ᵥ T₃ ▷ (actionʳ₂ ◁ F₁) ∘ᵥ T₃ ▷ associator.to ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
      actionʳ-∘ ∘ᵥ T₃ ▷ actionʳ-∘ ∎
      where
        open hom.HomReasoning

  abstract
    assoc-actionʳ-⊗-∘arr : (actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ associator.to) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq (T₃ ▷-coeq CoeqBimods))
                        ≈ (actionʳ-⊗ ∘ᵥ T₃ ▷ actionʳ-⊗) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq (T₃ ▷-coeq CoeqBimods))
    assoc-actionʳ-⊗-∘arr = begin
      (actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ associator.to) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq (T₃ ▷-coeq CoeqBimods)) ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗) ∘ᵥ associator.to) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq (T₃ ▷-coeq CoeqBimods)) ≈⟨ assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗) ∘ᵥ associator.to ∘ᵥ Coequalizer.arr (T₃ ▷-coeq (T₃ ▷-coeq CoeqBimods)) ≈⟨ refl⟩∘⟨ α⇐-▷-∘₁ ⟩
      (actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗) ∘ᵥ (T₃ ∘₁ T₃) ▷ Coequalizer.arr CoeqBimods ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ (T₃ ∘₁ T₃) ▷ Coequalizer.arr CoeqBimods ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ (μ₃ ◁ F-⊗ ∘ᵥ (T₃ ∘₁ T₃) ▷ Coequalizer.arr CoeqBimods) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionʳ-⊗ ∘ᵥ (T₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁)) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ ⟺ actionʳSq-⊗ ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘ ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ assoc-actionʳ-∘ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘ ∘ᵥ T₃ ▷ actionʳ-∘ ≈⟨ sym-assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ∘ᵥ T₃ ▷ actionʳ-∘ ≈⟨ actionʳSq-⊗ ⟩∘⟨refl ⟩
      (actionʳ-⊗ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ T₃ ▷ actionʳ-∘ ≈⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ T₃ ▷ actionʳ-∘ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
      actionʳ-⊗ ∘ᵥ T₃ ▷ (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ≈⟨ refl⟩∘⟨ ▷-resp-≈ actionʳSq-⊗ ⟩
      actionʳ-⊗ ∘ᵥ T₃ ▷ (actionʳ-⊗ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods) ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩
      actionʳ-⊗ ∘ᵥ T₃ ▷ actionʳ-⊗ ∘ᵥ Coequalizer.arr (T₃ ▷-coeq (T₃ ▷-coeq CoeqBimods)) ≈⟨ sym-assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ T₃ ▷ actionʳ-⊗) ∘ᵥ Coequalizer.arr (T₃ ▷-coeq (T₃ ▷-coeq CoeqBimods)) ∎
      where
        open hom.HomReasoning

  abstract
    assoc-actionʳ-⊗ : actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ associator.to ≈ actionʳ-⊗ ∘ᵥ T₃ ▷ actionʳ-⊗
    assoc-actionʳ-⊗ = Coequalizer⇒Epi (T₃ ▷-coeq (T₃ ▷-coeq CoeqBimods))
                                      (actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ associator.to)
                                      (actionʳ-⊗ ∘ᵥ T₃ ▷ actionʳ-⊗)
                                      assoc-actionʳ-⊗-∘arr
  abstract
    assoc-actionʳ-⊗-var : (actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗) ∘ᵥ associator.to ≈ actionʳ-⊗ ∘ᵥ T₃ ▷ actionʳ-⊗
    assoc-actionʳ-⊗-var = begin
      (actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗ ∘ᵥ associator.to ≈⟨ assoc-actionʳ-⊗ ⟩
      actionʳ-⊗ ∘ᵥ T₃ ▷ actionʳ-⊗ ∎
      where
        open hom.HomReasoning
  abstract
    sym-assoc-actionʳ-⊗ : actionʳ-⊗ ∘ᵥ T₃ ▷ actionʳ-⊗ ∘ᵥ associator.from ≈ actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗
    sym-assoc-actionʳ-⊗ = begin
      actionʳ-⊗ ∘ᵥ T₃ ▷ actionʳ-⊗ ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ T₃ ▷ actionʳ-⊗) ∘ᵥ associator.from ≈⟨ ⟺ (switch-tofromʳ associator assoc-actionʳ-⊗-var) ⟩
      actionʳ-⊗ ∘ᵥ μ₃ ◁ F-⊗ ∎
      where
        open hom.HomReasoning
        open import Categories.Morphism.Reasoning.Iso (hom C₁ C₃)
  -- end abstract --

module Identity where
  open Left-Action using (actionˡ-⊗; actionˡSq-⊗; actionˡ-∘)
  open Right-Action using (actionʳ-⊗; actionʳSq-⊗; actionʳ-∘)

  abstract
    identityˡ-∘ : actionˡ-∘ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈ id₂
    identityˡ-∘ = begin
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

  abstract
    identityˡ-⊗-∘arr : (actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈ id₂ ∘ᵥ Coequalizer.arr CoeqBimods
    identityˡ-⊗-∘arr = begin
      (actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ◁-∘ᵥ-ρ⇐ ⟩
      actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ Coequalizer.arr CoeqBimods ◁ id₁ ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ η₁ ∘ᵥ Coequalizer.arr CoeqBimods ◁ id₁) ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁) ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ sym-assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T₁) ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ ⟺ actionˡSq-⊗ ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ identityˡ-∘ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ id₂ ≈⟨ identity₂ʳ ⟩
      Coequalizer.arr CoeqBimods ≈⟨ ⟺ identity₂ˡ ⟩
      id₂ ∘ᵥ Coequalizer.arr CoeqBimods ∎
      where
        open hom.HomReasoning

  abstract
    identityˡ-⊗ : actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to ≈ id₂
    identityˡ-⊗ = Coequalizer⇒Epi CoeqBimods (actionˡ-⊗ ∘ᵥ F-⊗ ▷ η₁ ∘ᵥ unitorʳ.to) id₂ identityˡ-⊗-∘arr

  abstract
    identityʳ-∘ : actionʳ-∘ ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈ id₂
    identityʳ-∘ = begin
      actionʳ-∘ ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ assoc₂ ⟩
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

  abstract
    identityʳ-⊗-∘arr : (actionʳ-⊗ ∘ᵥ η₃ ◁ F-⊗ ∘ᵥ unitorˡ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈ id₂ ∘ᵥ Coequalizer.arr CoeqBimods
    identityʳ-⊗-∘arr = begin
      (actionʳ-⊗ ∘ᵥ η₃ ◁ F-⊗ ∘ᵥ unitorˡ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ (η₃ ◁ F-⊗ ∘ᵥ unitorˡ.to) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ η₃ ◁ F-⊗ ∘ᵥ unitorˡ.to ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ▷-∘ᵥ-λ⇐ ⟩
      actionʳ-⊗ ∘ᵥ η₃ ◁ F-⊗ ∘ᵥ id₁ ▷ Coequalizer.arr CoeqBimods ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ (η₃ ◁ F-⊗ ∘ᵥ id₁ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionʳ-⊗ ∘ᵥ (T₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁)) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ sym-assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ T₃ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ ⟺ actionʳSq-⊗ ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘ ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ identityʳ-∘ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ id₂ ≈⟨ identity₂ʳ ⟩
      Coequalizer.arr CoeqBimods ≈⟨ ⟺ identity₂ˡ ⟩
      id₂ ∘ᵥ Coequalizer.arr CoeqBimods ∎
      where
        open hom.HomReasoning

  abstract
    identityʳ-⊗ : actionʳ-⊗ ∘ᵥ (η₃ ◁ F-⊗) ∘ᵥ unitorˡ.to ≈ id₂
    identityʳ-⊗ = Coequalizer⇒Epi CoeqBimods (actionʳ-⊗ ∘ᵥ (η₃ ◁ F-⊗) ∘ᵥ unitorˡ.to) id₂ identityʳ-⊗-∘arr
  -- end abstract --

B₂⊗B₁ : Bimodule M₁ M₃
B₂⊗B₁ = record
  { F = F-⊗
  ; actionˡ = Left-Action.actionˡ-⊗                       -- : F ∘₁ T₁ ⇒₂ F
  ; actionʳ = Right-Action.actionʳ-⊗                      -- : T₂ ∘₁ F ⇒₂ F
  ; assoc = Associativity.assoc-⊗                         -- : actionʳ ∘ᵥ (T₂ ▷ actionˡ) ∘ᵥ associator.from ≈ actionˡ ∘ᵥ (actionʳ ◁ T₁)
  ; sym-assoc = Associativity.sym-assoc-⊗                 -- : actionˡ ∘ᵥ (actionʳ ◁ T₁)∘ᵥ associator.to ≈ actionʳ ∘ᵥ (T₂ ▷ actionˡ)
  ; assoc-actionˡ = Associativity.assoc-actionˡ-⊗         -- : actionˡ ∘ᵥ (F ▷ μ₁) ∘ᵥ associator.from ≈ actionˡ ∘ᵥ (actionˡ ◁ T₁)
  ; sym-assoc-actionˡ = Associativity.sym-assoc-actionˡ-⊗ -- : actionˡ ∘ᵥ (actionˡ ◁ T₁) ∘ᵥ associator.to ≈ actionˡ ∘ᵥ (F ▷ μ₁)
  ; assoc-actionʳ = Associativity.assoc-actionʳ-⊗         -- : actionʳ ∘ᵥ (μ₂ ◁ F) ∘ᵥ associator.to ≈ actionʳ ∘ᵥ (T₂ ▷ actionʳ)
  ; sym-assoc-actionʳ = Associativity.sym-assoc-actionʳ-⊗ -- : actionʳ ∘ᵥ (T₂ ▷ actionʳ) ∘ᵥ associator.from ≈ actionʳ ∘ᵥ (μ₂ ◁ F)
  ; identityˡ = Identity.identityˡ-⊗                      -- : actionˡ ∘ᵥ (F ▷ η₁) ∘ᵥ unitorʳ.to ≈ id₂
  ; identityʳ = Identity.identityʳ-⊗                      -- : actionʳ ∘ᵥ (η₂ ◁ F) ∘ᵥ unitorˡ.to ≈ id₂
  }
