{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers
open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule

module Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞}
  {M₁ M₂ M₃ : Monad 𝒞} (B₂ : Bimodule M₂ M₃) (B₁ : Bimodule M₁ M₂) where

open import Level
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands
open import Categories.Category

open LocalCoequalizers localCoeq
open ComposeWithLocalCoequalizer 𝒞 localCoeq using (_coeq-◁_; _▷-coeq_)

open Monad using (C; T; μ; η)
open Bimodule using (F; actionˡ; actionʳ; assoc; sym-assoc; assoc-actionˡ; assoc-actionʳ; identityˡ; identityʳ)

open import Categories.Diagram.Coequalizer (hom (C M₁) (C M₃)) using (Coequalizer; Coequalizer⇒Epi)
open import Categories.Diagram.Coequalizer.Properties (hom (C M₁) (C M₃)) using (⇒MapBetweenCoeq; ⇒MapBetweenCoeqSq)
import Categories.Category
open Categories.Category.Definitions (hom (C M₁) (C M₃)) using (CommutativeSquare)

import Categories.Morphism.Reasoning (hom (C M₁) (C M₃)) as MorphismReasoning
import Categories.Morphism.Reasoning.Iso (hom (C M₁) (C M₃)) as IsoReasoning

{-
To construct the tensorproduct B₂⊗B₁ we will define its underlying 1-cell
to be the coequalizer of the following parallel pair in hom (C M₁) (C M₃):

                      act-to-the-left
  F B₂ ∘ T M₂ ∘ F B₁ ==================> F B₂ ∘ F B₁
                      act-to-the-right
-}

-- We itroduce names to the two parallel morphism in the above diagram --
act-to-the-left act-to-the-right : F B₂ ∘₁ T M₂ ∘₁ F B₁   ⇒₂   F B₂ ∘₁ F B₁
act-to-the-left = F B₂ ▷ actionʳ B₁
act-to-the-right = actionˡ B₂ ◁ F B₁ ∘ᵥ α⇐

abstract
  -- to costruct the tensorproduct of bimodules the following coequalizer is formed --
  -- to speed-up type-checking we hide the definition of this coequalizer under an abstract clause --
  -- for all foreseeable purposes, the particular choice of coequalizer will not matter --
  CoeqBimods : Coequalizer        act-to-the-left act-to-the-right
  CoeqBimods = local-coequalizers act-to-the-left act-to-the-right
  
-- The underlying object of that coequalizer is the underlying 1-cell of the bimodule B₂⊗B₁ --
F-⊗ : C M₁ ⇒₁ C M₃
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

  actionˡ-∘-∘ : (F B₂ ∘₁ T M₂ ∘₁ F B₁) ∘₁ T M₁   ⇒₂   F B₂ ∘₁ T M₂ ∘₁ F B₁
  actionˡ-∘-∘ = α⇒ ∘ᵥ (F B₂ ∘₁ T M₂) ▷ actionˡ B₁ ∘ᵥ α⇒  ∘ᵥ α⇐ ◁ T M₁

  actionˡ-∘ : (F B₂ ∘₁ F B₁) ∘₁ T M₁ ⇒₂  F B₂ ∘₁ F B₁
  actionˡ-∘ = F B₂ ▷ actionˡ B₁ ∘ᵥ α⇒

  abstract
    private
      sq-act-to-the-left : CommutativeSquare
                             actionˡ-∘-∘
                             (act-to-the-left ◁ T M₁)
                             act-to-the-left
                             actionˡ-∘
      sq-act-to-the-left = begin
        act-to-the-left ∘ᵥ actionˡ-∘-∘                                                                 ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
        F B₂ ▷ actionʳ B₁ ∘ᵥ (α⇒ ∘ᵥ (F B₂ ∘₁ T M₂) ▷ actionˡ B₁) ∘ᵥ α⇒  ∘ᵥ α⇐ ◁ T M₁                   ≈⟨ refl⟩∘⟨ α⇒-▷-∘₁ ⟩∘⟨refl ⟩
        F B₂ ▷ actionʳ B₁ ∘ᵥ (F B₂ ▷ T M₂ ▷ actionˡ B₁ ∘ᵥ α⇒) ∘ᵥ α⇒  ∘ᵥ α⇐ ◁ T M₁                      ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        F B₂ ▷ actionʳ B₁ ∘ᵥ F B₂ ▷ T M₂ ▷ actionˡ B₁ ∘ᵥ α⇒ ∘ᵥ α⇒  ∘ᵥ α⇐ ◁ T M₁                        ≈⟨ ⟺ assoc₂ ⟩
        (F B₂ ▷ actionʳ B₁ ∘ᵥ F B₂ ▷ T M₂ ▷ actionˡ B₁) ∘ᵥ α⇒ ∘ᵥ α⇒  ∘ᵥ α⇐ ◁ T M₁                      ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
        (F B₂ ▷ actionʳ B₁ ∘ᵥ F B₂ ▷ T M₂ ▷ actionˡ B₁) ∘ᵥ (α⇒ ∘ᵥ α⇒) ∘ᵥ α⇐ ◁ T M₁                     ≈⟨ refl⟩∘⟨ ⟺ pentagon ⟩∘⟨refl ⟩
        -- maybe this can be shortened using conjugate --
        (F B₂ ▷ actionʳ B₁ ∘ᵥ F B₂ ▷ T M₂ ▷ actionˡ B₁) ∘ᵥ (F B₂ ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ T M₁) ∘ᵥ α⇐ ◁ T M₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        (F B₂ ▷ actionʳ B₁ ∘ᵥ F B₂ ▷ T M₂ ▷ actionˡ B₁) ∘ᵥ F B₂ ▷ α⇒ ∘ᵥ (α⇒ ∘ᵥ α⇒ ◁ T M₁) ∘ᵥ α⇐ ◁ T M₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩
        (F B₂ ▷ actionʳ B₁ ∘ᵥ F B₂ ▷ T M₂ ▷ actionˡ B₁) ∘ᵥ F B₂ ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ T M₁ ∘ᵥ α⇐ ◁ T M₁   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
        (F B₂ ▷ actionʳ B₁ ∘ᵥ F B₂ ▷ T M₂ ▷ actionˡ B₁) ∘ᵥ F B₂ ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ (α⇒ ∘ᵥ α⇐) ◁ T M₁        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ◁-resp-≈ associator.isoʳ ⟩
        (F B₂ ▷ actionʳ B₁ ∘ᵥ F B₂ ▷ T M₂ ▷ actionˡ B₁) ∘ᵥ F B₂ ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ id₂ ◁ T M₁               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ id₂◁ ⟩
        (F B₂ ▷ actionʳ B₁ ∘ᵥ F B₂ ▷ T M₂ ▷ actionˡ B₁) ∘ᵥ F B₂ ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ id₂                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ identity₂ʳ ⟩
        (F B₂ ▷ actionʳ B₁ ∘ᵥ F B₂ ▷ T M₂ ▷ actionˡ B₁) ∘ᵥ F B₂ ▷ α⇒ ∘ᵥ α⇒                             ≈⟨ ⟺ assoc₂ ⟩
        ((F B₂ ▷ actionʳ B₁ ∘ᵥ F B₂ ▷ T M₂ ▷ actionˡ B₁) ∘ᵥ F B₂ ▷ α⇒) ∘ᵥ α⇒                           ≈⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩∘⟨refl ⟩
        (F B₂ ▷ (actionʳ B₁ ∘ᵥ T M₂ ▷ actionˡ B₁) ∘ᵥ F B₂ ▷ α⇒) ∘ᵥ α⇒                                  ≈⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
        F B₂ ▷ ((actionʳ B₁ ∘ᵥ T M₂ ▷ actionˡ B₁) ∘ᵥ α⇒) ∘ᵥ α⇒                                         ≈⟨ ▷-resp-≈ assoc₂ ⟩∘⟨refl ⟩
        F B₂ ▷ (actionʳ B₁ ∘ᵥ T M₂ ▷ actionˡ B₁ ∘ᵥ α⇒) ∘ᵥ α⇒                                           ≈⟨ ▷-resp-≈ (assoc B₁) ⟩∘⟨refl ⟩
        F B₂ ▷ (actionˡ B₁ ∘ᵥ actionʳ B₁ ◁ T M₁) ∘ᵥ α⇒                                                 ≈⟨ ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
        (F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ (actionʳ B₁ ◁ T M₁)) ∘ᵥ α⇒                                        ≈⟨ assoc₂ ⟩
        F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ (actionʳ B₁ ◁ T M₁) ∘ᵥ α⇒                                          ≈⟨ refl⟩∘⟨ ⟺ α⇒-▷-◁ ⟩
        F B₂ ▷ actionˡ B₁ ∘ᵥ α⇒ ∘ᵥ (F B₂ ▷ actionʳ B₁) ◁ T M₁                                          ≈⟨ ⟺ assoc₂ ⟩
        actionˡ-∘ ∘ᵥ (act-to-the-left) ◁ T M₁                                                          ∎
        where
          open hom.HomReasoning

      sq-act-to-the-right : CommutativeSquare
                              actionˡ-∘-∘
                              (act-to-the-right ◁ T M₁)
                              act-to-the-right
                              actionˡ-∘
      sq-act-to-the-right = begin
        act-to-the-right ∘ᵥ actionˡ-∘-∘                                                     ≈⟨ ⟺ assoc₂ ⟩
        ((actionˡ B₂ ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ α⇒) ∘ᵥ (F B₂ ∘₁ T M₂) ▷ actionˡ B₁ ∘ᵥ α⇒ ∘ᵥ α⇐ ◁ T M₁ ≈⟨ assoc₂ ⟩∘⟨refl ⟩
        (actionˡ B₂ ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ α⇒) ∘ᵥ (F B₂ ∘₁ T M₂) ▷ actionˡ B₁ ∘ᵥ α⇒ ∘ᵥ α⇐ ◁ T M₁   ≈⟨ (refl⟩∘⟨ associator.isoˡ) ⟩∘⟨refl ⟩
        (actionˡ B₂ ◁ F B₁ ∘ᵥ id₂) ∘ᵥ (F B₂ ∘₁ T M₂) ▷ actionˡ B₁ ∘ᵥ α⇒ ∘ᵥ α⇐ ◁ T M₁        ≈⟨ identity₂ʳ ⟩∘⟨refl ⟩
        actionˡ B₂ ◁ F B₁ ∘ᵥ (F B₂ ∘₁ T M₂) ▷ actionˡ B₁ ∘ᵥ α⇒ ∘ᵥ α⇐ ◁ T M₁                 ≈⟨ ⟺ assoc₂ ⟩
        (actionˡ B₂ ◁ F B₁ ∘ᵥ (F B₂ ∘₁ T M₂) ▷ actionˡ B₁) ∘ᵥ α⇒ ∘ᵥ α⇐ ◁ T M₁               ≈⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
        (F B₂ ▷ actionˡ B₁ ∘ᵥ actionˡ B₂ ◁ (F B₁ ∘₁ T M₁)) ∘ᵥ α⇒ ∘ᵥ α⇐ ◁ T M₁               ≈⟨ assoc₂ ⟩
        F B₂ ▷ actionˡ B₁ ∘ᵥ actionˡ B₂ ◁ (F B₁ ∘₁ T M₁) ∘ᵥ α⇒ ∘ᵥ α⇐ ◁ T M₁                 ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
        F B₂ ▷ actionˡ B₁ ∘ᵥ (actionˡ B₂ ◁ (F B₁ ∘₁ T M₁) ∘ᵥ α⇒) ∘ᵥ α⇐ ◁ T M₁               ≈⟨ refl⟩∘⟨ ⟺ α⇒-◁-∘₁ ⟩∘⟨refl ⟩
        F B₂ ▷ actionˡ B₁ ∘ᵥ (α⇒ ∘ᵥ actionˡ B₂ ◁ F B₁ ◁ T M₁) ∘ᵥ α⇐ ◁ T M₁                  ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        F B₂ ▷ actionˡ B₁ ∘ᵥ α⇒ ∘ᵥ actionˡ B₂ ◁ F B₁ ◁ T M₁ ∘ᵥ α⇐ ◁ T M₁                    ≈⟨ ⟺ assoc₂ ⟩
        actionˡ-∘ ∘ᵥ actionˡ B₂ ◁ F B₁ ◁ T M₁ ∘ᵥ α⇐ ◁ T M₁                                  ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
        actionˡ-∘ ∘ᵥ act-to-the-right ◁ T M₁                                                ∎
        where
          open hom.HomReasoning
  -- end abstract --

  abstract    
    -- left-action --
    -- to speed-up type-checking we hide the definition of the left-action under an abstract clause --
    -- probably, no one ever wants to look into its defintion and instead only use the lemma actionˡSq-⊗ below --
    actionˡ-⊗ : F-⊗ ∘₁ T M₁ ⇒₂ F-⊗
    actionˡ-⊗ = ⇒MapBetweenCoeq
                  actionˡ-∘-∘
                  actionˡ-∘
                  sq-act-to-the-left
                  sq-act-to-the-right
                  (CoeqBimods coeq-◁ T M₁)
                  CoeqBimods

    -- the left-action fits into the following commutative square --
    actionˡSq-⊗ : CommutativeSquare
                    actionˡ-∘
                    (Coequalizer.arr (CoeqBimods coeq-◁ T M₁))
                    (Coequalizer.arr CoeqBimods)
                    actionˡ-⊗
    actionˡSq-⊗ = ⇒MapBetweenCoeqSq
                    actionˡ-∘-∘
                    actionˡ-∘
                    sq-act-to-the-left
                    sq-act-to-the-right
                    (CoeqBimods coeq-◁ T M₁)
                    CoeqBimods
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

  -- to define a map between the coequalizers T M₃ ∘₁ F-⊗ ⇒₂ F-⊗ we define a map of diagrams --
  actionʳ-∘-∘ : T M₃ ∘₁ F B₂ ∘₁ T M₂ ∘₁ F B₁ ⇒₂  F B₂ ∘₁ T M₂ ∘₁ F B₁
  actionʳ-∘-∘ = actionʳ B₂ ◁ (T M₂ ∘₁ F B₁) ∘ᵥ α⇐

  actionʳ-∘ : T M₃ ∘₁ F B₂ ∘₁ F B₁ ⇒₂  F B₂ ∘₁ F B₁
  actionʳ-∘ = actionʳ B₂ ◁ F B₁ ∘ᵥ α⇐

  -- to get a map of diagrams two squares have to commute --
  abstract
    private
      sq-act-to-the-left : CommutativeSquare
                             actionʳ-∘-∘
                             (T M₃ ▷ act-to-the-left)
                             act-to-the-left
                             actionʳ-∘
      sq-act-to-the-left = glue′ sq-bottom sq-top
        where
          open hom.HomReasoning
          open MorphismReasoning using (glue′)
          sq-top : CommutativeSquare
                     α⇐
                     (T M₃ ▷ F B₂ ▷ actionʳ B₁)
                     ((T M₃ ∘₁ F B₂) ▷ actionʳ B₁)
                     α⇐
          sq-top = ⟺ α⇐-▷-∘₁
          sq-bottom : CommutativeSquare
                        (actionʳ B₂ ◁ (T M₂ ∘₁ F B₁))
                        ((T M₃ ∘₁ F B₂) ▷ actionʳ B₁)
                        (F B₂ ▷ actionʳ B₁)
                        (actionʳ B₂ ◁ F B₁)
          sq-bottom = ◁-▷-exchg

      sq-act-to-the-right : CommutativeSquare
                              actionʳ-∘-∘
                              (T M₃ ▷ (act-to-the-right))
                              act-to-the-right
                              actionʳ-∘
      sq-act-to-the-right = begin
        act-to-the-right ∘ᵥ actionʳ-∘-∘                                                    ≈⟨ ⟺ assoc₂ ⟩
        ((actionˡ B₂ ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ actionʳ B₂ ◁  (T M₂ ∘₁ F B₁)) ∘ᵥ α⇐                  ≈⟨ assoc₂ ⟩∘⟨refl ⟩
        (actionˡ B₂ ◁ F B₁ ∘ᵥ (α⇐ ∘ᵥ actionʳ B₂ ◁  (T M₂ ∘₁ F B₁))) ∘ᵥ α⇐                  ≈⟨ (refl⟩∘⟨ α⇐-◁-∘₁) ⟩∘⟨refl ⟩
        (actionˡ B₂ ◁ F B₁ ∘ᵥ (actionʳ B₂ ◁ T M₂ ◁ F B₁ ∘ᵥ α⇐)) ∘ᵥ α⇐                      ≈⟨ assoc₂ ⟩
        actionˡ B₂ ◁ F B₁ ∘ᵥ ((actionʳ B₂ ◁ T M₂ ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ α⇐)                      ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        actionˡ B₂ ◁ F B₁ ∘ᵥ actionʳ B₂ ◁ T M₂ ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ α⇐                          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ pentagon-inv ⟩
        actionˡ B₂ ◁ F B₁ ∘ᵥ actionʳ B₂ ◁ T M₂ ◁ F B₁ ∘ᵥ (α⇐ ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇐    ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
        actionˡ B₂ ◁ F B₁ ∘ᵥ (actionʳ B₂ ◁ T M₂ ◁ F B₁ ∘ᵥ (α⇐ ◁ F B₁ ∘ᵥ α⇐)) ∘ᵥ T M₃ ▷ α⇐  ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩∘⟨refl ⟩
        actionˡ B₂ ◁ F B₁ ∘ᵥ ((actionʳ B₂ ◁ T M₂ ◁ F B₁ ∘ᵥ α⇐ ◁ F B₁) ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇐  ≈⟨ ⟺ assoc₂ ⟩
        (actionˡ B₂ ◁ F B₁ ∘ᵥ (actionʳ B₂ ◁ T M₂ ◁ F B₁ ∘ᵥ α⇐ ◁ F B₁) ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇐  ≈⟨ ⟺ assoc₂ ⟩∘⟨refl ⟩
        ((actionˡ B₂ ◁ F B₁ ∘ᵥ actionʳ B₂ ◁ T M₂ ◁ F B₁ ∘ᵥ α⇐ ◁ F B₁) ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇐  ≈⟨ ((refl⟩∘⟨ ∘ᵥ-distr-◁) ⟩∘⟨refl) ⟩∘⟨refl ⟩
        ((actionˡ B₂ ◁ F B₁ ∘ᵥ (actionʳ B₂ ◁ T M₂ ∘ᵥ α⇐) ◁ F B₁) ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇐       ≈⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩∘⟨refl ⟩
        ((actionˡ B₂ ∘ᵥ actionʳ B₂ ◁ T M₂ ∘ᵥ α⇐) ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇐                ≈⟨ ◁-resp-≈ (sym-assoc B₂) ⟩∘⟨refl ⟩∘⟨refl ⟩
        ((actionʳ B₂ ∘ᵥ (T M₃ ▷ actionˡ B₂)) ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇐                    ≈⟨ ⟺ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩∘⟨refl ⟩
        ((actionʳ B₂ ◁ F B₁ ∘ᵥ (T M₃ ▷ actionˡ B₂) ◁ F B₁) ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇐             ≈⟨ (assoc₂ ⟩∘⟨refl) ⟩
        (actionʳ B₂ ◁ F B₁ ∘ᵥ (T M₃ ▷ actionˡ B₂) ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇐               ≈⟨ (refl⟩∘⟨ ⟺ α⇐-▷-◁) ⟩∘⟨refl ⟩
        (actionʳ B₂ ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ (actionˡ B₂ ◁ F B₁)) ∘ᵥ T M₃ ▷ α⇐               ≈⟨ ⟺ assoc₂ ⟩∘⟨refl ⟩
        ((actionʳ B₂ ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ (actionˡ B₂ ◁ F B₁)) ∘ᵥ T M₃ ▷ α⇐             ≈⟨ assoc₂ ⟩
        (actionʳ B₂ ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ (actionˡ B₂ ◁ F B₁) ∘ᵥ T M₃ ▷ α⇐               ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
        actionʳ-∘ ∘ᵥ T M₃ ▷ act-to-the-right                                               ∎
          where
            open hom.HomReasoning
  -- end abstract --

  abstract
    -- right-action --
    -- to speed-up type-checking we hide the definition of the right-action under an abstract clause --
    -- probably, no one ever wants to look into its defintion and instead only use the lemma actionʳSq-⊗ below --
    actionʳ-⊗ : T M₃ ∘₁ F-⊗ ⇒₂ F-⊗
    actionʳ-⊗ = ⇒MapBetweenCoeq
                  actionʳ-∘-∘
                  actionʳ-∘
                  sq-act-to-the-left
                  sq-act-to-the-right
                  (T M₃ ▷-coeq CoeqBimods)
                  CoeqBimods

    -- the right-action fits into the following commutaitve square --
    actionʳSq-⊗ : CommutativeSquare (actionʳ-∘) (Coequalizer.arr (T M₃ ▷-coeq CoeqBimods)) (Coequalizer.arr CoeqBimods) (actionʳ-⊗)
    actionʳSq-⊗ = ⇒MapBetweenCoeqSq
                    actionʳ-∘-∘
                    actionʳ-∘
                    sq-act-to-the-left
                    sq-act-to-the-right
                    (T M₃ ▷-coeq CoeqBimods)
                    CoeqBimods
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
    assoc-∘ : actionʳ-∘ ∘ᵥ T M₃ ▷ actionˡ-∘ ∘ᵥ α⇒ ≈ actionˡ-∘ ∘ᵥ actionʳ-∘ ◁ T M₁
    assoc-∘ = begin
      actionʳ-∘ ∘ᵥ T M₃ ▷ actionˡ-∘ ∘ᵥ α⇒                                           ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
      actionʳ-∘ ∘ᵥ (T M₃ ▷ F B₂ ▷ actionˡ B₁ ∘ᵥ T M₃ ▷ α⇒) ∘ᵥ α⇒                    ≈⟨ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ (T M₃ ▷ F B₂ ▷ actionˡ B₁ ∘ᵥ T M₃ ▷ α⇒) ∘ᵥ α⇒      ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ (α⇐ ∘ᵥ (T M₃ ▷ F B₂ ▷ actionˡ B₁ ∘ᵥ T M₃ ▷ α⇒)) ∘ᵥ α⇒    ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩∘⟨refl ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ ((α⇐ ∘ᵥ T M₃ ▷ F B₂ ▷ actionˡ B₁) ∘ᵥ T M₃ ▷ α⇒) ∘ᵥ α⇒    ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ (α⇐ ∘ᵥ T M₃ ▷ F B₂ ▷ actionˡ B₁) ∘ᵥ T M₃ ▷ α⇒ ∘ᵥ α⇒      ≈⟨ refl⟩∘⟨ α⇐-▷-∘₁ ⟩∘⟨refl ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ ((T M₃ ∘₁ F B₂) ▷ actionˡ B₁ ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇒ ∘ᵥ α⇒   ≈⟨ ⟺ assoc₂ ⟩
      (actionʳ B₂ ◁ F B₁ ∘ᵥ ((T M₃ ∘₁ F B₂) ▷ actionˡ B₁ ∘ᵥ α⇐)) ∘ᵥ T M₃ ▷ α⇒ ∘ᵥ α⇒ ≈⟨ ⟺ assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ B₂ ◁ F B₁ ∘ᵥ (T M₃ ∘₁ F B₂) ▷ actionˡ B₁) ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇒ ∘ᵥ α⇒ ≈⟨ assoc₂ ⟩
      (actionʳ B₂ ◁ F B₁ ∘ᵥ (T M₃ ∘₁ F B₂) ▷ actionˡ B₁) ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ α⇒ ∘ᵥ α⇒   ≈⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
      (F B₂ ▷ actionˡ B₁ ∘ᵥ actionʳ B₂ ◁ (F B₁ ∘₁ T M₁)) ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ α⇒ ∘ᵥ α⇒   ≈⟨ refl⟩∘⟨ pentagon-conjugate₁ ⟩
      (F B₂ ▷ actionˡ B₁ ∘ᵥ actionʳ B₂ ◁ (F B₁ ∘₁ T M₁)) ∘ᵥ α⇒ ∘ᵥ α⇐ ◁ T M₁         ≈⟨ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ actionʳ B₂ ◁ (F B₁ ∘₁ T M₁) ∘ᵥ α⇒ ∘ᵥ α⇐ ◁ T M₁           ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ (actionʳ B₂ ◁ (F B₁ ∘₁ T M₁) ∘ᵥ α⇒) ∘ᵥ α⇐ ◁ T M₁         ≈⟨ refl⟩∘⟨ ⟺ α⇒-◁-∘₁ ⟩∘⟨refl ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ (α⇒ ∘ᵥ actionʳ B₂ ◁ F B₁ ◁ T M₁) ∘ᵥ α⇐ ◁ T M₁            ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ α⇒ ∘ᵥ actionʳ B₂ ◁ F B₁ ◁ T M₁ ∘ᵥ α⇐ ◁ T M₁              ≈⟨ ⟺ assoc₂ ⟩
      (F B₂ ▷ actionˡ B₁ ∘ᵥ α⇒) ∘ᵥ actionʳ B₂ ◁ F B₁ ◁ T M₁ ∘ᵥ α⇐ ◁ T M₁            ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-∘ ∘ᵥ actionʳ-∘ ◁ T M₁                                                 ∎
      where
        open hom.HomReasoning

  abstract
    assoc-⊗-∘arr : (actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗) ∘ᵥ α⇒) ∘ᵥ (Coequalizer.arr ((T M₃ ▷-coeq CoeqBimods) coeq-◁ T M₁))
                 ≈ (actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T M₁)) ∘ᵥ (Coequalizer.arr ((T M₃ ▷-coeq CoeqBimods) coeq-◁ T M₁))
    assoc-⊗-∘arr = begin
      (actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗) ∘ᵥ α⇒) ∘ᵥ (Coequalizer.arr ((T M₃ ▷-coeq CoeqBimods) coeq-◁ T M₁)) ≈⟨ ⟺ assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗)) ∘ᵥ α⇒) ∘ᵥ (Coequalizer.arr ((T M₃ ▷-coeq CoeqBimods) coeq-◁ T M₁)) ≈⟨ assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗)) ∘ᵥ α⇒ ∘ᵥ (Coequalizer.arr ((T M₃ ▷-coeq CoeqBimods) coeq-◁ T M₁)) ≈⟨ refl⟩∘⟨ α⇒-▷-◁ ⟩
      (actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗)) ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq (CoeqBimods coeq-◁ T M₁)) ∘ᵥ α⇒  ≈⟨ ⟺ assoc₂ ⟩
      ((actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗)) ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq (CoeqBimods coeq-◁ T M₁))) ∘ᵥ α⇒  ≈⟨ assoc₂ ⟩∘⟨refl ⟩
      (actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗) ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq (CoeqBimods coeq-◁ T M₁))) ∘ᵥ α⇒  ≈⟨ (refl⟩∘⟨ ∘ᵥ-distr-▷) ⟩∘⟨refl ⟩
      (actionʳ-⊗ ∘ᵥ T M₃ ▷ (actionˡ-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods coeq-◁ T M₁))) ∘ᵥ α⇒  ≈⟨ (refl⟩∘⟨ ▷-resp-≈ (⟺ actionˡSq-⊗)) ⟩∘⟨refl ⟩
      (actionʳ-⊗ ∘ᵥ T M₃ ▷ (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘)) ∘ᵥ α⇒  ≈⟨ (refl⟩∘⟨(⟺ ∘ᵥ-distr-▷)) ⟩∘⟨refl ⟩
      (actionʳ-⊗ ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq CoeqBimods) ∘ᵥ T M₃ ▷ actionˡ-∘) ∘ᵥ α⇒  ≈⟨ ⟺ assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ-⊗ ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq CoeqBimods)) ∘ᵥ T M₃ ▷ actionˡ-∘) ∘ᵥ α⇒  ≈⟨ (⟺ actionʳSq-⊗) ⟩∘⟨refl ⟩∘⟨refl ⟩
      ((Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ∘ᵥ T M₃ ▷ actionˡ-∘) ∘ᵥ α⇒  ≈⟨ assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ∘ᵥ T M₃ ▷ actionˡ-∘ ∘ᵥ α⇒  ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘ ∘ᵥ T M₃ ▷ actionˡ-∘ ∘ᵥ α⇒  ≈⟨ refl⟩∘⟨ assoc-∘ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ actionʳ-∘ ◁ T M₁  ≈⟨ ⟺ assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ actionʳ-∘ ◁ T M₁  ≈⟨ actionˡSq-⊗ ⟩∘⟨refl ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods coeq-◁ T M₁)) ∘ᵥ actionʳ-∘ ◁ T M₁  ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr (CoeqBimods coeq-◁ T M₁) ∘ᵥ actionʳ-∘ ◁ T M₁  ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ◁ T M₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ actionʳSq-⊗ ⟩
      actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq CoeqBimods)) ◁ T M₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ actionʳ-⊗ ◁ T M₁ ∘ᵥ Coequalizer.arr ((T M₃ ▷-coeq CoeqBimods) coeq-◁ T M₁) ≈⟨ ⟺ assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T M₁)) ∘ᵥ (Coequalizer.arr ((T M₃ ▷-coeq CoeqBimods) coeq-◁ T M₁)) ∎
      where
        open hom.HomReasoning

  abstract
    assoc-⊗ : actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗) ∘ᵥ α⇒ ≈ actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T M₁)
    assoc-⊗ = Coequalizer⇒Epi
                ((T M₃ ▷-coeq CoeqBimods) coeq-◁ T M₁)
                (actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗) ∘ᵥ α⇒)
                (actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T M₁))
                assoc-⊗-∘arr

  abstract
    assoc-⊗-var : (actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗)) ∘ᵥ α⇒ ≈ actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T M₁)
    assoc-⊗-var = begin
      (actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗)) ∘ᵥ α⇒ ≈⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗) ∘ᵥ α⇒   ≈⟨ assoc-⊗ ⟩
      actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T M₁)                      ∎
      where
        open hom.HomReasoning

  abstract
    sym-assoc-⊗ : actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T M₁) ∘ᵥ α⇐ ≈ actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗)
    sym-assoc-⊗ = begin
      actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T M₁) ∘ᵥ α⇐ ≈⟨ ⟺ assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionʳ-⊗ ◁ T M₁)) ∘ᵥ α⇐ ≈⟨ ⟺ (switch-fromtoʳ associator assoc-⊗-var) ⟩
      actionʳ-⊗ ∘ᵥ (T M₃ ▷ actionˡ-⊗) ∎
      where
        open hom.HomReasoning
        open IsoReasoning using (switch-fromtoʳ)

  abstract
    assoc-actionˡ-∘ : actionˡ-∘ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ μ M₁ ∘ᵥ α⇒ ≈ actionˡ-∘ ∘ᵥ actionˡ-∘ ◁ T M₁
    assoc-actionˡ-∘ = begin
      actionˡ-∘ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ μ M₁ ∘ᵥ α⇒ ≈⟨ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ α⇒ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ μ M₁ ∘ᵥ α⇒ ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ (α⇒ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ μ M₁) ∘ᵥ α⇒ ≈⟨ refl⟩∘⟨ α⇒-▷-∘₁ ⟩∘⟨refl ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ (F B₂ ▷ F B₁ ▷ μ M₁ ∘ᵥ α⇒) ∘ᵥ α⇒ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ F B₁ ▷ μ M₁ ∘ᵥ α⇒ ∘ᵥ α⇒ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ pentagon ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ F B₁ ▷ μ M₁ ∘ᵥ F B₂ ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ T M₁ ≈⟨ ⟺ assoc₂ ⟩
      (F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ F B₁ ▷ μ M₁) ∘ᵥ F B₂ ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ T M₁ ≈⟨ ⟺ assoc₂ ⟩
      ((F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ F B₁ ▷ μ M₁) ∘ᵥ F B₂ ▷ α⇒) ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ T M₁ ≈⟨ assoc₂ ⟩∘⟨refl ⟩
      (F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ F B₁ ▷ μ M₁ ∘ᵥ F B₂ ▷ α⇒) ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ T M₁ ≈⟨ (refl⟩∘⟨ ∘ᵥ-distr-▷) ⟩∘⟨refl ⟩
      (F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ (F B₁ ▷ μ M₁ ∘ᵥ α⇒)) ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ T M₁ ≈⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
      F B₂ ▷ (actionˡ B₁ ∘ᵥ F B₁ ▷ μ M₁ ∘ᵥ α⇒) ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ T M₁ ≈⟨ ▷-resp-≈ (assoc-actionˡ B₁) ⟩∘⟨refl ⟩
      F B₂ ▷ (actionˡ B₁ ∘ᵥ actionˡ B₁ ◁ T M₁) ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ T M₁ ≈⟨ ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
      (F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ (actionˡ B₁ ◁ T M₁)) ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ T M₁ ≈⟨ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ (actionˡ B₁ ◁ T M₁) ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ T M₁ ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ (F B₂ ▷ (actionˡ B₁ ◁ T M₁) ∘ᵥ α⇒) ∘ᵥ α⇒ ◁ T M₁ ≈⟨ refl⟩∘⟨ ⟺ α⇒-▷-◁ ⟩∘⟨refl ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ (α⇒ ∘ᵥ (F B₂ ▷ actionˡ B₁) ◁ T M₁) ∘ᵥ α⇒ ◁ T M₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ α⇒ ∘ᵥ (F B₂ ▷ actionˡ B₁) ◁ T M₁ ∘ᵥ α⇒ ◁ T M₁ ≈⟨ ⟺ assoc₂ ⟩
      (F B₂ ▷ actionˡ B₁ ∘ᵥ α⇒) ∘ᵥ (F B₂ ▷ actionˡ B₁) ◁ T M₁ ∘ᵥ α⇒ ◁ T M₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-∘ ∘ᵥ actionˡ-∘ ◁ T M₁ ∎
      where
        open hom.HomReasoning

  abstract
    assoc-actionˡ-⊗-∘arr : (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁) ∘ᵥ α⇒) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T M₁) coeq-◁ T M₁)
                         ≈ (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T M₁)) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T M₁) coeq-◁ T M₁)
    assoc-actionˡ-⊗-∘arr = begin
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁) ∘ᵥ α⇒) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T M₁) coeq-◁ T M₁) ≈⟨ ⟺ assoc₂ ⟩∘⟨refl ⟩
      ((actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁)) ∘ᵥ α⇒) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T M₁) coeq-◁ T M₁) ≈⟨ assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁)) ∘ᵥ α⇒ ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T M₁) coeq-◁ T M₁) ≈⟨ refl⟩∘⟨ α⇒-◁-∘₁ ⟩
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁)) ∘ᵥ Coequalizer.arr CoeqBimods ◁ (T M₁ ∘₁ T M₁) ∘ᵥ α⇒ ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁) ∘ᵥ Coequalizer.arr CoeqBimods ◁ (T M₁ ∘₁ T M₁) ∘ᵥ α⇒ ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ ((F-⊗ ▷ μ M₁) ∘ᵥ Coequalizer.arr CoeqBimods ◁ (T M₁ ∘₁ T M₁)) ∘ᵥ α⇒ ≈⟨ refl⟩∘⟨ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ◁ T M₁ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ μ M₁) ∘ᵥ α⇒ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T M₁ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ μ M₁ ∘ᵥ α⇒ ≈⟨ ⟺ assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T M₁) ∘ᵥ (F B₂ ∘₁ F B₁) ▷ μ M₁ ∘ᵥ α⇒ ≈⟨ ⟺ actionˡSq-⊗ ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ (F B₂ ∘₁ F B₁) ▷ μ M₁ ∘ᵥ α⇒ ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ μ M₁ ∘ᵥ α⇒ ≈⟨ refl⟩∘⟨ assoc-actionˡ-∘ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ actionˡ-∘ ◁ T M₁ ≈⟨ ⟺ assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ actionˡ-∘ ◁ T M₁ ≈⟨ actionˡSq-⊗ ⟩∘⟨refl ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T M₁) ∘ᵥ actionˡ-∘ ◁ T M₁ ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T M₁ ∘ᵥ actionˡ-∘ ◁ T M₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ◁ T M₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ actionˡSq-⊗ ⟩
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T M₁) ◁ T M₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T M₁) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T M₁) coeq-◁ T M₁) ≈⟨ ⟺ assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T M₁)) ∘ᵥ Coequalizer.arr ((CoeqBimods coeq-◁ T M₁) coeq-◁ T M₁) ∎
      where
        open hom.HomReasoning

  abstract
    assoc-actionˡ-⊗ : actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁) ∘ᵥ α⇒ ≈ actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T M₁)
    assoc-actionˡ-⊗ = Coequalizer⇒Epi
                        ((CoeqBimods coeq-◁ T M₁) coeq-◁ T M₁)
                        (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁) ∘ᵥ α⇒)
                        (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T M₁))
                        assoc-actionˡ-⊗-∘arr

  abstract
    assoc-actionˡ-⊗-var : (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁)) ∘ᵥ α⇒ ≈ actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T M₁)
    assoc-actionˡ-⊗-var = begin
      (actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁)) ∘ᵥ α⇒ ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁) ∘ᵥ α⇒ ≈⟨ assoc-actionˡ-⊗ ⟩
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T M₁) ∎
      where
        open hom.HomReasoning

  abstract
    sym-assoc-actionˡ-⊗ : actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T M₁) ∘ᵥ α⇐ ≈ actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁)
    sym-assoc-actionˡ-⊗ = begin
      actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T M₁) ∘ᵥ α⇐ ≈⟨ ⟺ assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ (actionˡ-⊗ ◁ T M₁)) ∘ᵥ α⇐ ≈⟨ ⟺ (switch-fromtoʳ associator assoc-actionˡ-⊗-var) ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ μ M₁) ∎
      where
        open hom.HomReasoning
        open IsoReasoning using (switch-fromtoʳ)
  -- end abstract --

  abstract
    assoc-actionʳ-∘ : actionʳ-∘ ∘ᵥ μ M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ α⇐ ≈ actionʳ-∘ ∘ᵥ T M₃ ▷ actionʳ-∘
    assoc-actionʳ-∘ = begin
      actionʳ-∘ ∘ᵥ μ M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ α⇐ ≈⟨ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ μ M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ (α⇐ ∘ᵥ μ M₃ ◁ (F B₂ ∘₁ F B₁)) ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ α⇐-◁-∘₁ ⟩∘⟨refl ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ (μ M₃ ◁ F B₂ ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ μ M₃ ◁ F B₂ ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ pentagon-inv ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ μ M₃ ◁ F B₂ ◁ F B₁ ∘ᵥ (α⇐ ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇐ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ μ M₃ ◁ F B₂ ◁ F B₁ ∘ᵥ α⇐ ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ α⇐ ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ (μ M₃ ◁ F B₂ ◁ F B₁ ∘ᵥ α⇐ ◁ F B₁) ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ α⇐ ≈⟨ ⟺ assoc₂ ⟩
      (actionʳ B₂ ◁ F B₁ ∘ᵥ μ M₃ ◁ F B₂ ◁ F B₁ ∘ᵥ α⇐ ◁ F B₁) ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ α⇐ ≈⟨ (refl⟩∘⟨ ∘ᵥ-distr-◁) ⟩∘⟨refl ⟩
      (actionʳ B₂ ◁ F B₁ ∘ᵥ (μ M₃ ◁ F B₂ ∘ᵥ α⇐) ◁ F B₁) ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ α⇐ ≈⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩
      (actionʳ B₂ ∘ᵥ μ M₃ ◁ F B₂ ∘ᵥ α⇐) ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ α⇐ ≈⟨ ◁-resp-≈ (assoc-actionʳ B₂) ⟩∘⟨refl ⟩
      (actionʳ B₂ ∘ᵥ T M₃ ▷ actionʳ B₂) ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ α⇐ ≈⟨ ⟺ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩
      (actionʳ B₂ ◁ F B₁ ∘ᵥ (T M₃ ▷ actionʳ B₂) ◁ F B₁) ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ α⇐ ≈⟨ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ (T M₃ ▷ actionʳ B₂) ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ α⇐ ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ ((T M₃ ▷ actionʳ B₂) ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ T M₃ ▷ α⇐ ≈⟨ refl⟩∘⟨ ⟺ α⇐-▷-◁ ⟩∘⟨refl ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ (α⇐ ∘ᵥ T M₃ ▷ (actionʳ B₂ ◁ F B₁)) ∘ᵥ T M₃ ▷ α⇐ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ T M₃ ▷ (actionʳ B₂ ◁ F B₁) ∘ᵥ T M₃ ▷ α⇐ ≈⟨ ⟺ assoc₂ ⟩
      actionʳ-∘ ∘ᵥ T M₃ ▷ (actionʳ B₂ ◁ F B₁) ∘ᵥ T M₃ ▷ α⇐ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
      actionʳ-∘ ∘ᵥ T M₃ ▷ actionʳ-∘ ∎
      where
        open hom.HomReasoning

  abstract
    assoc-actionʳ-⊗-∘arr : (actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗ ∘ᵥ α⇐) ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq (T M₃ ▷-coeq CoeqBimods))
                         ≈ (actionʳ-⊗ ∘ᵥ T M₃ ▷ actionʳ-⊗) ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq (T M₃ ▷-coeq CoeqBimods))
    assoc-actionʳ-⊗-∘arr = begin
      (actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗ ∘ᵥ α⇐) ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq (T M₃ ▷-coeq CoeqBimods)) ≈⟨ ⟺ assoc₂ ⟩∘⟨refl ⟩
      ((actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗) ∘ᵥ α⇐) ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq (T M₃ ▷-coeq CoeqBimods)) ≈⟨ assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗) ∘ᵥ α⇐ ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq (T M₃ ▷-coeq CoeqBimods)) ≈⟨ refl⟩∘⟨ α⇐-▷-∘₁ ⟩
      (actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗) ∘ᵥ (T M₃ ∘₁ T M₃) ▷ Coequalizer.arr CoeqBimods ∘ᵥ α⇐ ≈⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗ ∘ᵥ (T M₃ ∘₁ T M₃) ▷ Coequalizer.arr CoeqBimods ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ (μ M₃ ◁ F-⊗ ∘ᵥ (T M₃ ∘₁ T M₃) ▷ Coequalizer.arr CoeqBimods) ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionʳ-⊗ ∘ᵥ (T M₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ μ M₃ ◁ (F B₂ ∘₁ F B₁)) ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ T M₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ μ M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ α⇐ ≈⟨ ⟺ assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ T M₃ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ μ M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ α⇐ ≈⟨ ⟺ actionʳSq-⊗ ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ∘ᵥ μ M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ α⇐ ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘ ∘ᵥ μ M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ assoc-actionʳ-∘ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘ ∘ᵥ T M₃ ▷ actionʳ-∘ ≈⟨ ⟺ assoc₂ ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ∘ᵥ T M₃ ▷ actionʳ-∘ ≈⟨ actionʳSq-⊗ ⟩∘⟨refl ⟩
      (actionʳ-⊗ ∘ᵥ T M₃ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ T M₃ ▷ actionʳ-∘ ≈⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ T M₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ T M₃ ▷ actionʳ-∘ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
      actionʳ-⊗ ∘ᵥ T M₃ ▷ (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ≈⟨ refl⟩∘⟨ ▷-resp-≈ actionʳSq-⊗ ⟩
      actionʳ-⊗ ∘ᵥ T M₃ ▷ (actionʳ-⊗ ∘ᵥ T M₃ ▷ Coequalizer.arr CoeqBimods) ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩
      actionʳ-⊗ ∘ᵥ T M₃ ▷ actionʳ-⊗ ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq (T M₃ ▷-coeq CoeqBimods)) ≈⟨ ⟺ assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ T M₃ ▷ actionʳ-⊗) ∘ᵥ Coequalizer.arr (T M₃ ▷-coeq (T M₃ ▷-coeq CoeqBimods)) ∎
      where
        open hom.HomReasoning

  abstract
    assoc-actionʳ-⊗ : actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗ ∘ᵥ α⇐ ≈ actionʳ-⊗ ∘ᵥ T M₃ ▷ actionʳ-⊗
    assoc-actionʳ-⊗ = Coequalizer⇒Epi
                        (T M₃ ▷-coeq (T M₃ ▷-coeq CoeqBimods))
                        (actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗ ∘ᵥ α⇐)
                        (actionʳ-⊗ ∘ᵥ T M₃ ▷ actionʳ-⊗)
                        assoc-actionʳ-⊗-∘arr
  abstract
    assoc-actionʳ-⊗-var : (actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗) ∘ᵥ α⇐ ≈ actionʳ-⊗ ∘ᵥ T M₃ ▷ actionʳ-⊗
    assoc-actionʳ-⊗-var = begin
      (actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗) ∘ᵥ α⇐ ≈⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗ ∘ᵥ α⇐ ≈⟨ assoc-actionʳ-⊗ ⟩
      actionʳ-⊗ ∘ᵥ T M₃ ▷ actionʳ-⊗ ∎
      where
        open hom.HomReasoning
  abstract
    sym-assoc-actionʳ-⊗ : actionʳ-⊗ ∘ᵥ T M₃ ▷ actionʳ-⊗ ∘ᵥ α⇒ ≈ actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗
    sym-assoc-actionʳ-⊗ = begin
      actionʳ-⊗ ∘ᵥ T M₃ ▷ actionʳ-⊗ ∘ᵥ α⇒ ≈⟨ ⟺ assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ T M₃ ▷ actionʳ-⊗) ∘ᵥ α⇒ ≈⟨ ⟺ (switch-tofromʳ associator assoc-actionʳ-⊗-var) ⟩
      actionʳ-⊗ ∘ᵥ μ M₃ ◁ F-⊗ ∎
      where
        open hom.HomReasoning
        open IsoReasoning using (switch-tofromʳ)
  -- end abstract --

module Identity where
  open Left-Action using (actionˡ-⊗; actionˡSq-⊗; actionˡ-∘)
  open Right-Action using (actionʳ-⊗; actionʳSq-⊗; actionʳ-∘)

  abstract
    identityˡ-∘ : actionˡ-∘ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ η M₁ ∘ᵥ ρ⇐ ≈ id₂
    identityˡ-∘ = begin
      actionˡ-∘ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ η M₁ ∘ᵥ ρ⇐ ≈⟨ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ α⇒ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ η M₁ ∘ᵥ ρ⇐ ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ (α⇒ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ η M₁) ∘ᵥ ρ⇐ ≈⟨ refl⟩∘⟨ α⇒-▷-∘₁ ⟩∘⟨refl ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ (F B₂ ▷ F B₁ ▷ η M₁ ∘ᵥ α⇒) ∘ᵥ ρ⇐ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ F B₁ ▷ η M₁ ∘ᵥ α⇒ ∘ᵥ ρ⇐ ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ ⟺ unitorʳ-coherence-var₂) ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ F B₁ ▷ η M₁ ∘ᵥ F B₂ ▷ ρ⇐ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
      F B₂ ▷ actionˡ B₁ ∘ᵥ F B₂ ▷ (F B₁ ▷ η M₁ ∘ᵥ ρ⇐) ≈⟨ ∘ᵥ-distr-▷ ⟩
      F B₂ ▷ (actionˡ B₁ ∘ᵥ F B₁ ▷ η M₁ ∘ᵥ ρ⇐) ≈⟨ ▷-resp-≈ (identityˡ B₁) ⟩
      F B₂ ▷ id₂ ≈⟨ ▷id₂ ⟩
      id₂ ∎
      where
        open hom.HomReasoning

  abstract
    identityˡ-⊗-∘arr : (actionˡ-⊗ ∘ᵥ F-⊗ ▷ η M₁ ∘ᵥ ρ⇐) ∘ᵥ Coequalizer.arr CoeqBimods ≈ id₂ ∘ᵥ Coequalizer.arr CoeqBimods
    identityˡ-⊗-∘arr = begin
      (actionˡ-⊗ ∘ᵥ F-⊗ ▷ η M₁ ∘ᵥ ρ⇐) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ η M₁ ∘ᵥ ρ⇐) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ F-⊗ ▷ η M₁ ∘ᵥ ρ⇐ ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ◁-∘ᵥ-ρ⇐ ⟩
      actionˡ-⊗ ∘ᵥ F-⊗ ▷ η M₁ ∘ᵥ Coequalizer.arr CoeqBimods ◁ id₁ ∘ᵥ ρ⇐ ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ (F-⊗ ▷ η M₁ ∘ᵥ Coequalizer.arr CoeqBimods ◁ id₁) ∘ᵥ ρ⇐ ≈⟨ refl⟩∘⟨ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionˡ-⊗ ∘ᵥ (Coequalizer.arr CoeqBimods ◁ T M₁ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ η M₁) ∘ᵥ ρ⇐ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T M₁ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ η M₁ ∘ᵥ ρ⇐ ≈⟨ ⟺ assoc₂ ⟩
      (actionˡ-⊗ ∘ᵥ Coequalizer.arr CoeqBimods ◁ T M₁) ∘ᵥ (F B₂ ∘₁ F B₁) ▷ η M₁ ∘ᵥ ρ⇐ ≈⟨ ⟺ actionˡSq-⊗ ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘) ∘ᵥ (F B₂ ∘₁ F B₁) ▷ η M₁ ∘ᵥ ρ⇐ ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionˡ-∘ ∘ᵥ (F B₂ ∘₁ F B₁) ▷ η M₁ ∘ᵥ ρ⇐ ≈⟨ refl⟩∘⟨ identityˡ-∘ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ id₂ ≈⟨ identity₂ʳ ⟩
      Coequalizer.arr CoeqBimods ≈⟨ ⟺ identity₂ˡ ⟩
      id₂ ∘ᵥ Coequalizer.arr CoeqBimods ∎
      where
        open hom.HomReasoning

  abstract
    identityˡ-⊗ : actionˡ-⊗ ∘ᵥ F-⊗ ▷ η M₁ ∘ᵥ ρ⇐ ≈ id₂
    identityˡ-⊗ = Coequalizer⇒Epi
                    CoeqBimods
                    (actionˡ-⊗ ∘ᵥ F-⊗ ▷ η M₁ ∘ᵥ ρ⇐)
                    id₂
                    identityˡ-⊗-∘arr

  abstract
    identityʳ-∘ : actionʳ-∘ ∘ᵥ η M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ λ⇐ ≈ id₂
    identityʳ-∘ = begin
      actionʳ-∘ ∘ᵥ η M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ λ⇐ ≈⟨ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ η M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ λ⇐ ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ (α⇐ ∘ᵥ η M₃ ◁ (F B₂ ∘₁ F B₁)) ∘ᵥ λ⇐ ≈⟨ refl⟩∘⟨ α⇐-◁-∘₁ ⟩∘⟨refl ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ (η M₃ ◁ F B₂ ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ λ⇐ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ η M₃ ◁ F B₂ ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ λ⇐ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ unitorˡ-coherence-inv ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ η M₃ ◁ F B₂ ◁ F B₁ ∘ᵥ λ⇐ ◁ F B₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
      actionʳ B₂ ◁ F B₁ ∘ᵥ (η M₃ ◁ F B₂ ∘ᵥ λ⇐) ◁ F B₁ ≈⟨ ∘ᵥ-distr-◁ ⟩
      (actionʳ B₂ ∘ᵥ η M₃ ◁ F B₂ ∘ᵥ λ⇐) ◁ F B₁ ≈⟨ ◁-resp-≈ (identityʳ B₂) ⟩
      id₂ ◁ F B₁ ≈⟨ id₂◁ ⟩
      id₂ ∎
      where
        open hom.HomReasoning

  abstract
    identityʳ-⊗-∘arr : (actionʳ-⊗ ∘ᵥ η M₃ ◁ F-⊗ ∘ᵥ λ⇐) ∘ᵥ Coequalizer.arr CoeqBimods ≈ id₂ ∘ᵥ Coequalizer.arr CoeqBimods
    identityʳ-⊗-∘arr = begin
      (actionʳ-⊗ ∘ᵥ η M₃ ◁ F-⊗ ∘ᵥ λ⇐) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ (η M₃ ◁ F-⊗ ∘ᵥ λ⇐) ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ η M₃ ◁ F-⊗ ∘ᵥ λ⇐ ∘ᵥ Coequalizer.arr CoeqBimods ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ▷-∘ᵥ-λ⇐ ⟩
      actionʳ-⊗ ∘ᵥ η M₃ ◁ F-⊗ ∘ᵥ id₁ ▷ Coequalizer.arr CoeqBimods ∘ᵥ λ⇐ ≈⟨ refl⟩∘⟨ ⟺ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ (η M₃ ◁ F-⊗ ∘ᵥ id₁ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ λ⇐ ≈⟨ refl⟩∘⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
      actionʳ-⊗ ∘ᵥ (T M₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ η M₃ ◁ (F B₂ ∘₁ F B₁)) ∘ᵥ λ⇐ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      actionʳ-⊗ ∘ᵥ T M₃ ▷ Coequalizer.arr CoeqBimods ∘ᵥ η M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ λ⇐ ≈⟨ ⟺ assoc₂ ⟩
      (actionʳ-⊗ ∘ᵥ T M₃ ▷ Coequalizer.arr CoeqBimods) ∘ᵥ η M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ λ⇐ ≈⟨ ⟺ actionʳSq-⊗ ⟩∘⟨refl ⟩
      (Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘) ∘ᵥ η M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ λ⇐ ≈⟨ assoc₂ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ actionʳ-∘ ∘ᵥ η M₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ λ⇐ ≈⟨ refl⟩∘⟨ identityʳ-∘ ⟩
      Coequalizer.arr CoeqBimods ∘ᵥ id₂ ≈⟨ identity₂ʳ ⟩
      Coequalizer.arr CoeqBimods ≈⟨ ⟺ identity₂ˡ ⟩
      id₂ ∘ᵥ Coequalizer.arr CoeqBimods ∎
      where
        open hom.HomReasoning

  abstract
    identityʳ-⊗ : actionʳ-⊗ ∘ᵥ (η M₃ ◁ F-⊗) ∘ᵥ λ⇐ ≈ id₂
    identityʳ-⊗ = Coequalizer⇒Epi
                    CoeqBimods
                    (actionʳ-⊗ ∘ᵥ (η M₃ ◁ F-⊗) ∘ᵥ λ⇐)
                    id₂
                    identityʳ-⊗-∘arr
  -- end abstract --


Tensorproduct : Bimodule M₁ M₃
Tensorproduct = record
  { F = F-⊗
  ; actionˡ = Left-Action.actionˡ-⊗                       -- : F ∘₁ T M₁ ⇒₂ F
  ; actionʳ = Right-Action.actionʳ-⊗                      -- : T M₂ ∘₁ F ⇒₂ F
  ; assoc = Associativity.assoc-⊗                         -- : actionʳ ∘ᵥ (T M₂ ▷ actionˡ) ∘ᵥ α⇒ ≈ actionˡ ∘ᵥ (actionʳ ◁ T M₁)
  ; sym-assoc = Associativity.sym-assoc-⊗                 -- : actionˡ ∘ᵥ (actionʳ ◁ T M₁)∘ᵥ α⇐ ≈ actionʳ ∘ᵥ (T M₂ ▷ actionˡ)
  ; assoc-actionˡ = Associativity.assoc-actionˡ-⊗         -- : actionˡ ∘ᵥ (F ▷ μ M₁) ∘ᵥ α⇒ ≈ actionˡ ∘ᵥ (actionˡ ◁ T M₁)
  ; sym-assoc-actionˡ = Associativity.sym-assoc-actionˡ-⊗ -- : actionˡ ∘ᵥ (actionˡ ◁ T M₁) ∘ᵥ α⇐ ≈ actionˡ ∘ᵥ (F ▷ μ M₁)
  ; assoc-actionʳ = Associativity.assoc-actionʳ-⊗         -- : actionʳ ∘ᵥ (μ M₂ ◁ F) ∘ᵥ α⇐ ≈ actionʳ ∘ᵥ (T M₂ ▷ actionʳ)
  ; sym-assoc-actionʳ = Associativity.sym-assoc-actionʳ-⊗ -- : actionʳ ∘ᵥ (T M₂ ▷ actionʳ) ∘ᵥ α⇒ ≈ actionʳ ∘ᵥ (μ M₂ ◁ F)
  ; identityˡ = Identity.identityˡ-⊗                      -- : actionˡ ∘ᵥ (F ▷ η M₁) ∘ᵥ ρ⇐ ≈ id₂
  ; identityʳ = Identity.identityʳ-⊗                      -- : actionʳ ∘ᵥ (η M₂ ◁ F) ∘ᵥ λ⇐ ≈ id₂
  }
