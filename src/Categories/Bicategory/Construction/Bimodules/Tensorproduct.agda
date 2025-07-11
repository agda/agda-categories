{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

module Categories.Bicategory.Construction.Bimodules.Tensorproduct
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} where

open import Categories.Bicategory.Monad
open import Level
open import Categories.Bicategory.Monad.Bimodule
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


module TensorproductOfBimodules {M₁ M₂ M₃ : Monad 𝒞} (B₂ : Bimodule M₂ M₃) (B₁ : Bimodule M₁ M₂) where

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
  
                         F₂ ▷ actionʳ₁
  F₂ ∘₁ T₂ ∘ F₁ ==============================> F₂ ∘₁ F₁
                actionˡ₂ ◁ F₁ ∘ᵥ associator.to
  -}

  -- We itroduce names to the two parallel morphism in the above diagram --
  act-to-the-left act-to-the-right : F₂ ∘₁ T₂ ∘₁ F₁ ⇒₂ F₂ ∘₁ F₁
  act-to-the-left = F₂ ▷ actionʳ₁
  act-to-the-right = actionˡ₂ ◁ F₁ ∘ᵥ associator.to


  -- The coequalizer that defines the composite bimodule --
  F₂⊗F₁ : Coequalizer (hom C₁ C₃) (act-to-the-left) (act-to-the-right)
  F₂⊗F₁ = localCoequalizers C₁ C₃ (act-to-the-left) (act-to-the-right)
  -- coequalizer {_} {_} {F₂ ∘₁ T₂ ∘₁ F₁} {F₂ ∘₁ F₁} (act-to-the-left) (act-to-the-right)

  -- The underlying object of that coequalizer is the underlying 1-cell of the bimodule B₂⊗B₁ --
  F : C₁ ⇒₁ C₃
  F = Coequalizer.obj F₂⊗F₁


  module Left-Action where

    -- To define the left-action we need that F ∘₁ T₁ is a coequalizer --
    F∘T₁Coequalizer : Coequalizer (hom C₁ C₃) ((act-to-the-left) ◁ T₁) ((act-to-the-right) ◁ T₁)
    F∘T₁Coequalizer = F₂⊗F₁ coeq-◁ T₁
    
    F₂∘₁T₂▷actionˡ₁ : (F₂ ∘₁ T₂ ∘₁ F₁) ∘₁ T₁ ⇒₂ F₂ ∘₁ T₂ ∘₁ F₁
    F₂∘₁T₂▷actionˡ₁ = associator.from ∘ᵥ (F₂ ∘₁ T₂) ▷ actionˡ₁ ∘ᵥ associator.from  ∘ᵥ associator.to ◁ T₁

    F₂▷actionˡ₁ : (F₂ ∘₁ F₁) ∘₁ T₁ ⇒₂  F₂ ∘₁ F₁
    F₂▷actionˡ₁ = F₂ ▷ actionˡ₁ ∘ᵥ associator.from

    -- for CommutativeSquare --
    open Definitions (hom C₁ C₃)

    abstract
      sq₁ : CommutativeSquare (F₂∘₁T₂▷actionˡ₁) ((act-to-the-left) ◁ T₁) (act-to-the-left) (F₂▷actionˡ₁)
      sq₁ = begin
        act-to-the-left ∘ᵥ F₂∘₁T₂▷actionˡ₁                                     ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
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
          ∘ᵥ associator.from                                                 ≈⟨ ▷-resp-≈ assoc₂ ⟩∘⟨ refl ⟩
        F₂ ▷ (actionʳ₁ ∘ᵥ T₂ ▷ actionˡ₁ ∘ᵥ associator.from)
          ∘ᵥ associator.from ≈⟨ ▷-resp-≈ action-assoc₁ ⟩∘⟨refl ⟩
        F₂ ▷ (actionˡ₁ ∘ᵥ actionʳ₁ ◁ T₁) ∘ᵥ associator.from                  ≈⟨ ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
        (F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ (actionʳ₁ ◁ T₁)) ∘ᵥ associator.from           ≈⟨ assoc₂ ⟩
        F₂ ▷ actionˡ₁ ∘ᵥ F₂ ▷ (actionʳ₁ ◁ T₁) ∘ᵥ associator.from             ≈⟨ refl⟩∘⟨ ⟺ α⇒-▷-◁ ⟩
        F₂ ▷ actionˡ₁ ∘ᵥ associator.from ∘ᵥ (F₂ ▷ actionʳ₁) ◁ T₁             ≈⟨ ⟺ assoc₂ ⟩
        F₂▷actionˡ₁ ∘ᵥ (act-to-the-left) ◁ T₁ ∎
        where
          open hom.HomReasoning
          open hom.Equiv

      sq₂ : CommutativeSquare (F₂∘₁T₂▷actionˡ₁) ((act-to-the-right) ◁ T₁) (act-to-the-right) (F₂▷actionˡ₁)
      sq₂ = begin
        (act-to-the-right) ∘ᵥ F₂∘₁T₂▷actionˡ₁                               ≈⟨ sym-assoc₂ ⟩
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
        F₂▷actionˡ₁ ∘ᵥ actionˡ₂ ◁ F₁ ◁ T₁ ∘ᵥ associator.to ◁ T₁                           ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
        F₂▷actionˡ₁ ∘ᵥ (act-to-the-right) ◁ T₁ ∎
        where
          open hom.HomReasoning
          open hom.Equiv
    -- end abstract --
    
    -- left-action --
    actionˡ : F ∘₁ T₁ ⇒₂ F
    actionˡ = ⇒MapBetweenCoeq F₂∘₁T₂▷actionˡ₁ F₂▷actionˡ₁ sq₁ sq₂ F∘T₁Coequalizer F₂⊗F₁
      where
        open CoeqProperties (hom C₁ C₃)
        
    abstract    
      -- the left-action fits into the following commutaitve square --
      actionˡSq : CommutativeSquare (F₂▷actionˡ₁) (Coequalizer.arr F∘T₁Coequalizer) (Coequalizer.arr F₂⊗F₁) (actionˡ)
      actionˡSq = ⇒MapBetweenCoeqSq F₂∘₁T₂▷actionˡ₁ F₂▷actionˡ₁ sq₁ sq₂ F∘T₁Coequalizer F₂⊗F₁
        where
          open CoeqProperties (hom C₁ C₃)
    -- end abstract --

  module Right-Action where

    -- To define the right-action we need that T₃ ∘₁ F is a coequalizer --
    T₃∘FCoequalizer : Coequalizer (hom C₁ C₃) (T₃ ▷ (act-to-the-left)) (T₃ ▷ (act-to-the-right))
    T₃∘FCoequalizer =  T₃ ▷-coeq F₂⊗F₁

    -- to define a map between the coequalizers T₃ ∘₁ F ⇒₂ F we define a map of diagrams --
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
    actionʳ : T₃ ∘₁ F ⇒₂ F
    actionʳ = ⇒MapBetweenCoeq actionʳ₂◁T₂∘₁F₁ actionʳ₂◁F₁ sq₁ sq₂ T₃∘FCoequalizer F₂⊗F₁
      where
        open CoeqProperties (hom C₁ C₃)

    abstract
      -- the right-action fits into the following commutaitve square --
      actionʳSq : CommutativeSquare (actionʳ₂◁F₁) (Coequalizer.arr T₃∘FCoequalizer) (Coequalizer.arr F₂⊗F₁) (actionʳ)
      actionʳSq = ⇒MapBetweenCoeqSq actionʳ₂◁T₂∘₁F₁ actionʳ₂◁F₁ sq₁ sq₂ T₃∘FCoequalizer F₂⊗F₁
        where
          open CoeqProperties (hom C₁ C₃)
    -- end abstract --

  module Associativity where
    open Left-Action using (actionˡ; actionˡSq; F₂▷actionˡ₁; F∘T₁Coequalizer)
    open Right-Action using (actionʳ; actionʳSq; actionʳ₂◁F₁; T₃∘FCoequalizer)

    -- we need that T₃∘(F∘T₁) is a coequalizer --
    T₃∘[F∘T₁]Coequalizer : Coequalizer (hom C₁ C₃) (T₃ ▷ ((act-to-the-left) ◁ T₁))  (T₃ ▷ ((act-to-the-right) ◁ T₁))
    T₃∘[F∘T₁]Coequalizer = T₃ ▷-coeq F∘T₁Coequalizer

    -- we need that (T₃∘F)∘T₁ is a coequalizer --
    [T₃∘F]∘T₁Coequalizer : Coequalizer (hom C₁ C₃) ((T₃ ▷ (act-to-the-left)) ◁ T₁) ((T₃ ▷ (act-to-the-right)) ◁ T₁)
    [T₃∘F]∘T₁Coequalizer = T₃∘FCoequalizer coeq-◁ T₁

    abstract
      assoc-pentagon : actionʳ₂◁F₁ ∘ᵥ T₃ ▷ F₂▷actionˡ₁ ∘ᵥ associator.from ≈ F₂▷actionˡ₁ ∘ᵥ actionʳ₂◁F₁ ◁ T₁
      assoc-pentagon = begin
        actionʳ₂◁F₁ ∘ᵥ T₃ ▷ F₂▷actionˡ₁ ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ (⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl) ⟩
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
        F₂▷actionˡ₁ ∘ᵥ actionʳ₂◁F₁ ◁ T₁ ∎
        where
          open hom.HomReasoning

      assoc∘arr : (actionʳ ∘ᵥ (T₃ ▷ actionˡ) ∘ᵥ associator.from) ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer)
                  ≈ (actionˡ ∘ᵥ (actionʳ ◁ T₁)) ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer)
      assoc∘arr = begin
        (actionʳ ∘ᵥ (T₃ ▷ actionˡ) ∘ᵥ associator.from) ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer) ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
        ((actionʳ ∘ᵥ (T₃ ▷ actionˡ)) ∘ᵥ associator.from) ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer) ≈⟨ assoc₂ ⟩
        (actionʳ ∘ᵥ (T₃ ▷ actionˡ)) ∘ᵥ associator.from ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer) ≈⟨ refl⟩∘⟨ α⇒-▷-◁ ⟩
        (actionʳ ∘ᵥ (T₃ ▷ actionˡ)) ∘ᵥ Coequalizer.arr T₃∘[F∘T₁]Coequalizer ∘ᵥ associator.from  ≈⟨ sym-assoc₂ ⟩
        ((actionʳ ∘ᵥ (T₃ ▷ actionˡ)) ∘ᵥ Coequalizer.arr T₃∘[F∘T₁]Coequalizer) ∘ᵥ associator.from  ≈⟨ assoc₂ ⟩∘⟨refl ⟩
        (actionʳ ∘ᵥ (T₃ ▷ actionˡ) ∘ᵥ Coequalizer.arr T₃∘[F∘T₁]Coequalizer) ∘ᵥ associator.from  ≈⟨ (refl⟩∘⟨ ∘ᵥ-distr-▷) ⟩∘⟨refl ⟩
        (actionʳ ∘ᵥ T₃ ▷ (actionˡ ∘ᵥ Coequalizer.arr F∘T₁Coequalizer)) ∘ᵥ associator.from  ≈⟨ (refl⟩∘⟨ ▷-resp-≈ (⟺ actionˡSq)) ⟩∘⟨refl ⟩
        (actionʳ ∘ᵥ T₃ ▷ (Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂▷actionˡ₁)) ∘ᵥ associator.from  ≈⟨ (refl⟩∘⟨(⟺ ∘ᵥ-distr-▷)) ⟩∘⟨refl ⟩
        (actionʳ ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ∘ᵥ T₃ ▷ F₂▷actionˡ₁) ∘ᵥ associator.from  ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
        ((actionʳ ∘ᵥ Coequalizer.arr T₃∘FCoequalizer) ∘ᵥ T₃ ▷ F₂▷actionˡ₁) ∘ᵥ associator.from  ≈⟨ (⟺ actionʳSq) ⟩∘⟨refl ⟩∘⟨refl ⟩
        ((Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁) ∘ᵥ T₃ ▷ F₂▷actionˡ₁) ∘ᵥ associator.from  ≈⟨ assoc₂ ⟩
        (Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁) ∘ᵥ T₃ ▷ F₂▷actionˡ₁ ∘ᵥ associator.from  ≈⟨ assoc₂ ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁ ∘ᵥ T₃ ▷ F₂▷actionˡ₁ ∘ᵥ associator.from  ≈⟨ refl⟩∘⟨ assoc-pentagon ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂▷actionˡ₁ ∘ᵥ actionʳ₂◁F₁ ◁ T₁  ≈⟨ sym-assoc₂ ⟩
        (Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂▷actionˡ₁) ∘ᵥ actionʳ₂◁F₁ ◁ T₁  ≈⟨ actionˡSq ⟩∘⟨refl ⟩
        (actionˡ ∘ᵥ Coequalizer.arr F∘T₁Coequalizer) ∘ᵥ actionʳ₂◁F₁ ◁ T₁  ≈⟨ assoc₂ ⟩
        actionˡ ∘ᵥ Coequalizer.arr F∘T₁Coequalizer ∘ᵥ actionʳ₂◁F₁ ◁ T₁  ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
        actionˡ ∘ᵥ (Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ actionʳSq ⟩
        actionˡ ∘ᵥ (actionʳ ∘ᵥ Coequalizer.arr T₃∘FCoequalizer) ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
        actionˡ ∘ᵥ actionʳ ◁ T₁ ∘ᵥ Coequalizer.arr [T₃∘F]∘T₁Coequalizer ≈⟨ sym-assoc₂ ⟩
        (actionˡ ∘ᵥ (actionʳ ◁ T₁)) ∘ᵥ (Coequalizer.arr [T₃∘F]∘T₁Coequalizer) ∎
        where
          open hom.HomReasoning
    
      assoc : actionʳ ∘ᵥ (T₃ ▷ actionˡ) ∘ᵥ associator.from ≈ actionˡ ∘ᵥ (actionʳ ◁ T₁)
      assoc = Coequalizer⇒Epi (hom C₁ C₃) [T₃∘F]∘T₁Coequalizer
                              (actionʳ ∘ᵥ (T₃ ▷ actionˡ) ∘ᵥ associator.from)
                              (actionˡ ∘ᵥ (actionʳ ◁ T₁))
                              assoc∘arr

      assoc-var : (actionʳ ∘ᵥ (T₃ ▷ actionˡ)) ∘ᵥ associator.from ≈ actionˡ ∘ᵥ (actionʳ ◁ T₁)
      assoc-var = begin
        (actionʳ ∘ᵥ (T₃ ▷ actionˡ)) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
        actionʳ ∘ᵥ (T₃ ▷ actionˡ) ∘ᵥ associator.from ≈⟨ assoc ⟩
        actionˡ ∘ᵥ (actionʳ ◁ T₁) ∎
        where
          open hom.HomReasoning

      sym-assoc : actionˡ ∘ᵥ (actionʳ ◁ T₁) ∘ᵥ associator.to ≈ actionʳ ∘ᵥ (T₃ ▷ actionˡ)
      sym-assoc = begin
        actionˡ ∘ᵥ (actionʳ ◁ T₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
        (actionˡ ∘ᵥ (actionʳ ◁ T₁)) ∘ᵥ associator.to ≈⟨ ⟺ (switch-fromtoʳ associator assoc-var) ⟩
        actionʳ ∘ᵥ (T₃ ▷ actionˡ) ∎
        where
          open hom.HomReasoning
          open import Categories.Morphism.Reasoning.Iso (hom C₁ C₃)

    -- end abstarct --

    --  we need that (F∘T₁)∘T₁ is a coequalizer --
    [F∘T₁]∘T₁Coequalizer : Coequalizer (hom C₁ C₃) (((act-to-the-left) ◁ T₁) ◁ T₁) (((act-to-the-right) ◁ T₁) ◁ T₁)
    [F∘T₁]∘T₁Coequalizer = F∘T₁Coequalizer coeq-◁ T₁

    abstract
      assoc-actionˡ-pentagon : F₂▷actionˡ₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈ F₂▷actionˡ₁ ∘ᵥ F₂▷actionˡ₁ ◁ T₁
      assoc-actionˡ-pentagon = begin
        F₂▷actionˡ₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
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
        F₂▷actionˡ₁ ∘ᵥ F₂▷actionˡ₁ ◁ T₁ ∎
        where
          open hom.HomReasoning

      assoc-actionˡ∘arr : (actionˡ ∘ᵥ (F ▷ μ₁) ∘ᵥ associator.from) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer
                          ≈ (actionˡ ∘ᵥ (actionˡ ◁ T₁)) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer
      assoc-actionˡ∘arr = begin
        (actionˡ ∘ᵥ (F ▷ μ₁) ∘ᵥ associator.from) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
        ((actionˡ ∘ᵥ (F ▷ μ₁)) ∘ᵥ associator.from) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer ≈⟨ assoc₂ ⟩
        (actionˡ ∘ᵥ (F ▷ μ₁)) ∘ᵥ associator.from ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer ≈⟨ refl⟩∘⟨ α⇒-◁-∘₁ ⟩
        (actionˡ ∘ᵥ (F ▷ μ₁)) ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ (T₁ ∘₁ T₁) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
        actionˡ ∘ᵥ (F ▷ μ₁) ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ (T₁ ∘₁ T₁) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
        actionˡ ∘ᵥ ((F ▷ μ₁) ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ (T₁ ∘₁ T₁)) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ ◁-▷-exchg ⟩∘⟨refl ⟩
        actionˡ ∘ᵥ (Coequalizer.arr F₂⊗F₁ ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁) ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        actionˡ ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩
        (actionˡ ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ T₁) ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ ⟺ actionˡSq ⟩∘⟨refl ⟩
        (Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂▷actionˡ₁) ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂▷actionˡ₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ μ₁ ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ assoc-actionˡ-pentagon ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂▷actionˡ₁ ∘ᵥ F₂▷actionˡ₁ ◁ T₁ ≈⟨ sym-assoc₂ ⟩
        (Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂▷actionˡ₁) ∘ᵥ F₂▷actionˡ₁ ◁ T₁ ≈⟨ actionˡSq ⟩∘⟨refl ⟩
        (actionˡ ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ T₁) ∘ᵥ F₂▷actionˡ₁ ◁ T₁ ≈⟨ assoc₂ ⟩
        actionˡ ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ T₁ ∘ᵥ F₂▷actionˡ₁ ◁ T₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
        actionˡ ∘ᵥ (Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂▷actionˡ₁) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ actionˡSq ⟩
        actionˡ ∘ᵥ (actionˡ ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ T₁) ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
        actionˡ ∘ᵥ (actionˡ ◁ T₁) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer ≈⟨ sym-assoc₂ ⟩
        (actionˡ ∘ᵥ (actionˡ ◁ T₁)) ∘ᵥ Coequalizer.arr [F∘T₁]∘T₁Coequalizer ∎
        where
          open hom.HomReasoning

      assoc-actionˡ : actionˡ ∘ᵥ (F ▷ μ₁) ∘ᵥ associator.from ≈ actionˡ ∘ᵥ (actionˡ ◁ T₁)
      assoc-actionˡ = Coequalizer⇒Epi ((hom C₁ C₃)) [F∘T₁]∘T₁Coequalizer
                                      (actionˡ ∘ᵥ (F ▷ μ₁) ∘ᵥ associator.from)
                                      (actionˡ ∘ᵥ (actionˡ ◁ T₁))
                                      assoc-actionˡ∘arr

      assoc-actionˡ-var : (actionˡ ∘ᵥ (F ▷ μ₁)) ∘ᵥ associator.from ≈ actionˡ ∘ᵥ (actionˡ ◁ T₁)
      assoc-actionˡ-var = begin
        (actionˡ ∘ᵥ (F ▷ μ₁)) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
        actionˡ ∘ᵥ (F ▷ μ₁) ∘ᵥ associator.from ≈⟨ assoc-actionˡ ⟩
        actionˡ ∘ᵥ (actionˡ ◁ T₁) ∎
        where
          open hom.HomReasoning

      sym-assoc-actionˡ : actionˡ ∘ᵥ (actionˡ ◁ T₁) ∘ᵥ associator.to ≈ actionˡ ∘ᵥ (F ▷ μ₁)
      sym-assoc-actionˡ = begin
        actionˡ ∘ᵥ (actionˡ ◁ T₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
        (actionˡ ∘ᵥ (actionˡ ◁ T₁)) ∘ᵥ associator.to ≈⟨ ⟺ (switch-fromtoʳ associator assoc-actionˡ-var) ⟩
        actionˡ ∘ᵥ (F ▷ μ₁) ∎
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

      assoc-actionʳ∘arr : (actionʳ ∘ᵥ μ₃ ◁ F ∘ᵥ associator.to) ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer
                          ≈ (actionʳ ∘ᵥ T₃ ▷ actionʳ) ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer
      assoc-actionʳ∘arr = begin
        (actionʳ ∘ᵥ μ₃ ◁ F ∘ᵥ associator.to) ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩
        ((actionʳ ∘ᵥ μ₃ ◁ F) ∘ᵥ associator.to) ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer ≈⟨ assoc₂ ⟩
        (actionʳ ∘ᵥ μ₃ ◁ F) ∘ᵥ associator.to ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer ≈⟨ refl⟩∘⟨ α⇐-▷-∘₁ ⟩
        (actionʳ ∘ᵥ μ₃ ◁ F) ∘ᵥ (T₃ ∘₁ T₃) ▷ Coequalizer.arr F₂⊗F₁ ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
        actionʳ ∘ᵥ μ₃ ◁ F ∘ᵥ (T₃ ∘₁ T₃) ▷ Coequalizer.arr F₂⊗F₁ ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
        actionʳ ∘ᵥ (μ₃ ◁ F ∘ᵥ (T₃ ∘₁ T₃) ▷ Coequalizer.arr F₂⊗F₁) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
        actionʳ ∘ᵥ (T₃ ▷ Coequalizer.arr F₂⊗F₁ ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁)) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr F₂⊗F₁ ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
        (actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr F₂⊗F₁) ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ ⟺ actionʳSq ⟩∘⟨refl ⟩
        (Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁) ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁ ∘ᵥ μ₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ assoc-actionʳ-pentagon ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁ ∘ᵥ T₃ ▷ actionʳ₂◁F₁ ≈⟨ sym-assoc₂ ⟩
        (Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁) ∘ᵥ T₃ ▷ actionʳ₂◁F₁ ≈⟨ actionʳSq ⟩∘⟨refl ⟩
        (actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr F₂⊗F₁) ∘ᵥ T₃ ▷ actionʳ₂◁F₁ ≈⟨ assoc₂ ⟩
        actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr F₂⊗F₁ ∘ᵥ T₃ ▷ actionʳ₂◁F₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
        actionʳ ∘ᵥ T₃ ▷ (Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁) ≈⟨ refl⟩∘⟨ ▷-resp-≈ actionʳSq ⟩
        actionʳ ∘ᵥ T₃ ▷ (actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr F₂⊗F₁) ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩
        actionʳ ∘ᵥ T₃ ▷ actionʳ ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer ≈⟨ sym-assoc₂ ⟩
        (actionʳ ∘ᵥ T₃ ▷ actionʳ) ∘ᵥ Coequalizer.arr T₃∘[T₃∘F]Coequalizer ∎
        where
          open hom.HomReasoning

      assoc-actionʳ : actionʳ ∘ᵥ μ₃ ◁ F ∘ᵥ associator.to ≈ actionʳ ∘ᵥ T₃ ▷ actionʳ
      assoc-actionʳ = Coequalizer⇒Epi (hom C₁ C₃) T₃∘[T₃∘F]Coequalizer
                                      (actionʳ ∘ᵥ μ₃ ◁ F ∘ᵥ associator.to)
                                      (actionʳ ∘ᵥ T₃ ▷ actionʳ)
                                      assoc-actionʳ∘arr

      assoc-actionʳ-var : (actionʳ ∘ᵥ μ₃ ◁ F) ∘ᵥ associator.to ≈ actionʳ ∘ᵥ T₃ ▷ actionʳ
      assoc-actionʳ-var = begin
        (actionʳ ∘ᵥ μ₃ ◁ F) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
        actionʳ ∘ᵥ μ₃ ◁ F ∘ᵥ associator.to ≈⟨ assoc-actionʳ ⟩
        actionʳ ∘ᵥ T₃ ▷ actionʳ ∎
        where
          open hom.HomReasoning

      sym-assoc-actionʳ : actionʳ ∘ᵥ T₃ ▷ actionʳ ∘ᵥ associator.from ≈ actionʳ ∘ᵥ μ₃ ◁ F
      sym-assoc-actionʳ = begin
        actionʳ ∘ᵥ T₃ ▷ actionʳ ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩
        (actionʳ ∘ᵥ T₃ ▷ actionʳ) ∘ᵥ associator.from ≈⟨ ⟺ (switch-tofromʳ associator assoc-actionʳ-var) ⟩
        actionʳ ∘ᵥ μ₃ ◁ F ∎
        where
          open hom.HomReasoning
          open import Categories.Morphism.Reasoning.Iso (hom C₁ C₃)
    -- end abstract --

  module Identity where
    open Left-Action using (actionˡ; actionˡSq; F₂▷actionˡ₁; F∘T₁Coequalizer)
    open Right-Action using (actionʳ; actionʳSq; actionʳ₂◁F₁; T₃∘FCoequalizer)

    abstract
      identityˡ-triangle : F₂▷actionˡ₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈ id₂
      identityˡ-triangle = begin
        F₂▷actionˡ₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ assoc₂ ⟩
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

      identityˡ∘arr : (actionˡ ∘ᵥ F ▷ η₁ ∘ᵥ unitorʳ.to) ∘ᵥ Coequalizer.arr F₂⊗F₁ ≈ id₂ ∘ᵥ Coequalizer.arr F₂⊗F₁
      identityˡ∘arr = begin
        (actionˡ ∘ᵥ F ▷ η₁ ∘ᵥ unitorʳ.to) ∘ᵥ Coequalizer.arr F₂⊗F₁ ≈⟨ assoc₂ ⟩
        actionˡ ∘ᵥ (F ▷ η₁ ∘ᵥ unitorʳ.to) ∘ᵥ Coequalizer.arr F₂⊗F₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        actionˡ ∘ᵥ F ▷ η₁ ∘ᵥ unitorʳ.to ∘ᵥ Coequalizer.arr F₂⊗F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ◁-∘ᵥ-ρ⇐ ⟩
        actionˡ ∘ᵥ F ▷ η₁ ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ id₁ ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
        actionˡ ∘ᵥ (F ▷ η₁ ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ id₁) ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ ◁-▷-exchg ⟩∘⟨refl ⟩
        actionˡ ∘ᵥ (Coequalizer.arr F₂⊗F₁ ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁) ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        actionˡ ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ T₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ sym-assoc₂ ⟩
        (actionˡ ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ T₁) ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ ⟺ actionˡSq ⟩∘⟨refl ⟩
        (Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂▷actionˡ₁) ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ assoc₂ ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂▷actionˡ₁ ∘ᵥ (F₂ ∘₁ F₁) ▷ η₁ ∘ᵥ unitorʳ.to ≈⟨ refl⟩∘⟨ identityˡ-triangle ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ id₂ ≈⟨ identity₂ʳ ⟩
        Coequalizer.arr F₂⊗F₁ ≈⟨ ⟺ identity₂ˡ ⟩
        id₂ ∘ᵥ Coequalizer.arr F₂⊗F₁ ∎
        where
          open hom.HomReasoning

      identityˡ : actionˡ ∘ᵥ F ▷ η₁ ∘ᵥ unitorʳ.to ≈ id₂
      identityˡ = Coequalizer⇒Epi (hom C₁ C₃) F₂⊗F₁ (actionˡ ∘ᵥ F ▷ η₁ ∘ᵥ unitorʳ.to) id₂ identityˡ∘arr


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

      identityʳ∘arr : (actionʳ ∘ᵥ η₃ ◁ F ∘ᵥ unitorˡ.to) ∘ᵥ Coequalizer.arr F₂⊗F₁ ≈ id₂ ∘ᵥ Coequalizer.arr F₂⊗F₁
      identityʳ∘arr = begin
        (actionʳ ∘ᵥ η₃ ◁ F ∘ᵥ unitorˡ.to) ∘ᵥ Coequalizer.arr F₂⊗F₁ ≈⟨ assoc₂ ⟩
        actionʳ ∘ᵥ (η₃ ◁ F ∘ᵥ unitorˡ.to) ∘ᵥ Coequalizer.arr F₂⊗F₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        actionʳ ∘ᵥ η₃ ◁ F ∘ᵥ unitorˡ.to ∘ᵥ Coequalizer.arr F₂⊗F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ▷-∘ᵥ-λ⇐ ⟩
        actionʳ ∘ᵥ η₃ ◁ F ∘ᵥ id₁ ▷ Coequalizer.arr F₂⊗F₁ ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
        actionʳ ∘ᵥ (η₃ ◁ F ∘ᵥ id₁ ▷ Coequalizer.arr F₂⊗F₁) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
        actionʳ ∘ᵥ (T₃ ▷ Coequalizer.arr F₂⊗F₁ ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁)) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr F₂⊗F₁ ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ sym-assoc₂ ⟩
        (actionʳ ∘ᵥ T₃ ▷ Coequalizer.arr F₂⊗F₁) ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ ⟺ actionʳSq ⟩∘⟨refl ⟩
        (Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁) ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ assoc₂ ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁ ∘ᵥ η₃ ◁ (F₂ ∘₁ F₁) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ identityʳ-triangle ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ id₂ ≈⟨ identity₂ʳ ⟩
        Coequalizer.arr F₂⊗F₁ ≈⟨ ⟺ identity₂ˡ ⟩
        id₂ ∘ᵥ Coequalizer.arr F₂⊗F₁ ∎
        where
          open hom.HomReasoning

      identityʳ : actionʳ ∘ᵥ (η₃ ◁ F) ∘ᵥ unitorˡ.to ≈ id₂
      identityʳ = Coequalizer⇒Epi (hom C₁ C₃) F₂⊗F₁ (actionʳ ∘ᵥ (η₃ ◁ F) ∘ᵥ unitorˡ.to) id₂ identityʳ∘arr
    -- end abstract --

  B₂⊗B₁ : Bimodule M₁ M₃
  B₂⊗B₁ = record
    { F = F
    ; actionˡ = Left-Action.actionˡ --: F ∘₁ T₁ ⇒₂ F  
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



module TensorproductOfHomomorphisms {M₁ M₂ M₃ : Monad 𝒞} {B₂ B'₂ : Bimodule M₂ M₃} {B₁ B'₁ : Bimodule M₁ M₂}
                                    (h₂ : Bimodulehomomorphism B₂ B'₂) (h₁ : Bimodulehomomorphism B₁ B'₁) where
  open Monad M₁ using () renaming (C to C₁; T to T₁; μ to μ₁; η to η₁)
  open Monad M₂ using () renaming (C to C₂; T to T₂; μ to μ₂; η to η₂)
  open Monad M₃ using () renaming (C to C₃; T to T₃; μ to μ₃; η to η₃)
  open Bimodule B₁ using () renaming (F to F₁; actionʳ to actionʳ₁; actionˡ to actionˡ₁)
  open Bimodule B'₁ using () renaming (F to F'₁; actionʳ to actionʳ'₁; actionˡ to actionˡ'₁)
  open Bimodule B₂ using () renaming (F to F₂; actionʳ to actionʳ₂; actionˡ to actionˡ₂)
  open Bimodule B'₂ using () renaming (F to F'₂; actionʳ to actionʳ'₂; actionˡ to actionˡ'₂)
  open TensorproductOfBimodules B₂ B₁ using (B₂⊗B₁; F₂⊗F₁; act-to-the-left; act-to-the-right)
  open TensorproductOfBimodules B'₂ B'₁ using ()
    renaming (B₂⊗B₁ to B'₂⊗B'₁; F₂⊗F₁ to F'₂⊗F'₁; act-to-the-left to act-to-the-left'; act-to-the-right to act-to-the-right')
  open Bimodule B₂⊗B₁ using (F; actionˡ; actionʳ)
  open Bimodule B'₂⊗B'₁ using () renaming (F to F'; actionˡ to actionˡ'; actionʳ to actionʳ')
  open Bimodulehomomorphism h₁ using () renaming (α to α₁; linearˡ to linearˡ₁; linearʳ to linearʳ₁)
  open Bimodulehomomorphism h₂ using () renaming (α to α₂; linearˡ to linearˡ₂; linearʳ to linearʳ₂)

  open Definitions (hom C₁ C₃) -- for Commutative Squares

  sq₁ : CommutativeSquare (α₂ ⊚₁ id₂ ⊚₁ α₁)
                          (act-to-the-left)
                          (act-to-the-left')
                          (α₂ ⊚₁ α₁)
  sq₁ = begin
    act-to-the-left' ∘ᵥ α₂ ⊚₁ id₂ ⊚₁ α₁ ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩
    (id₂ ∘ᵥ α₂) ⊚₁ (actionʳ'₁ ∘ᵥ id₂ ⊚₁ α₁) ≈⟨ identity₂ˡ ⟩⊚⟨ linearʳ₁ ⟩
    α₂ ⊚₁ (α₁ ∘ᵥ actionʳ₁) ≈⟨ ⟺ identity₂ʳ ⟩⊚⟨refl ⟩
    (α₂ ∘ᵥ id₂) ⊚₁ (α₁ ∘ᵥ actionʳ₁) ≈⟨ ∘ᵥ-distr-⊚ ⟩
    α₂ ⊚₁ α₁ ∘ᵥ act-to-the-left ∎
    where
      open hom.HomReasoning

  sq₂ : CommutativeSquare (α₂ ⊚₁ id₂ ⊚₁ α₁)
                          (act-to-the-right)
                          (act-to-the-right')
                          (α₂ ⊚₁ α₁)
  sq₂ = begin
    act-to-the-right' ∘ᵥ α₂ ⊚₁ id₂ ⊚₁ α₁ ≈⟨ assoc₂ ⟩
    actionˡ'₂ ◁ F'₁ ∘ᵥ associator.to ∘ᵥ α₂ ⊚₁ id₂ ⊚₁ α₁ ≈⟨ refl⟩∘⟨ α⇐-⊚ ⟩
    actionˡ'₂ ◁ F'₁ ∘ᵥ (α₂ ⊚₁ id₂) ⊚₁ α₁ ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
    (actionˡ'₂ ◁ F'₁ ∘ᵥ (α₂ ⊚₁ id₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
    ((actionˡ'₂ ∘ᵥ (α₂ ⊚₁ id₂)) ⊚₁ (id₂ ∘ᵥ α₁)) ∘ᵥ associator.to ≈⟨ linearˡ₂ ⟩⊚⟨refl ⟩∘⟨refl ⟩
    ((α₂ ∘ᵥ actionˡ₂) ⊚₁ (id₂ ∘ᵥ α₁)) ∘ᵥ associator.to ≈⟨ refl⟩⊚⟨ identity₂ˡ ⟩∘⟨refl ⟩
    ((α₂ ∘ᵥ actionˡ₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ refl⟩⊚⟨ ⟺ identity₂ʳ ⟩∘⟨refl ⟩
    ((α₂ ∘ᵥ actionˡ₂) ⊚₁ (α₁ ∘ᵥ id₂)) ∘ᵥ associator.to ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
    (α₂ ⊚₁ α₁ ∘ᵥ actionˡ₂ ◁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
    α₂ ⊚₁ α₁ ∘ᵥ act-to-the-right ∎
    where
      open hom.HomReasoning

  α : F ⇒₂ F'
  α = ⇒MapBetweenCoeq (α₂ ⊚₁ id₂ ⊚₁  α₁) (α₂ ⊚₁ α₁) sq₁ sq₂ F₂⊗F₁ F'₂⊗F'₁
    where
      open CoeqProperties (hom C₁ C₃)

  αSq : CommutativeSquare (α₂ ⊚₁ α₁) (Coequalizer.arr F₂⊗F₁) (Coequalizer.arr F'₂⊗F'₁) α
  αSq = ⇒MapBetweenCoeqSq (α₂ ⊚₁ id₂ ⊚₁  α₁) (α₂ ⊚₁ α₁) sq₁ sq₂ F₂⊗F₁ F'₂⊗F'₁
    where
      open CoeqProperties (hom C₁ C₃)

  open TensorproductOfBimodules.Left-Action B₂ B₁ using (F∘T₁Coequalizer; F₂▷actionˡ₁; actionˡSq)
  open TensorproductOfBimodules.Left-Action B'₂ B'₁ using ()
    renaming (F₂▷actionˡ₁ to F'₂▷actionˡ'₁; actionˡSq to actionˡ'Sq)

  linearˡ-square :  F'₂▷actionˡ'₁ ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈ (α₂ ⊚₁ α₁) ∘ᵥ F₂▷actionˡ₁
  linearˡ-square = begin
    F'₂▷actionˡ'₁ ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ assoc₂ ⟩
    F'₂ ▷ actionˡ'₁ ∘ᵥ associator.from ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ refl⟩∘⟨ α⇒-⊚ ⟩
    F'₂ ▷ actionˡ'₁ ∘ᵥ α₂ ⊚₁ (α₁ ◁ T₁) ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩
    (F'₂ ▷ actionˡ'₁ ∘ᵥ α₂ ⊚₁ (α₁ ◁ T₁)) ∘ᵥ associator.from ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
    ((id₂ ∘ᵥ α₂) ⊚₁ (actionˡ'₁ ∘ᵥ α₁ ◁ T₁)) ∘ᵥ associator.from ≈⟨ identity₂ˡ ⟩⊚⟨ linearˡ₁ ⟩∘⟨refl ⟩
    (α₂ ⊚₁ (α₁ ∘ᵥ actionˡ₁)) ∘ᵥ associator.from ≈⟨ ⟺ identity₂ʳ ⟩⊚⟨refl ⟩∘⟨refl ⟩
    ((α₂ ∘ᵥ id₂) ⊚₁ (α₁ ∘ᵥ actionˡ₁)) ∘ᵥ associator.from ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
    ((α₂ ⊚₁ α₁) ∘ᵥ F₂ ▷ actionˡ₁) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
    (α₂ ⊚₁ α₁) ∘ᵥ F₂▷actionˡ₁ ∎
    where
      open hom.HomReasoning

  linearˡ∘arr : (actionˡ' ∘ᵥ α ◁ T₁) ∘ᵥ Coequalizer.arr F∘T₁Coequalizer
                ≈ (α ∘ᵥ actionˡ) ∘ᵥ Coequalizer.arr F∘T₁Coequalizer
  linearˡ∘arr = begin
    (actionˡ' ∘ᵥ α ◁ T₁) ∘ᵥ Coequalizer.arr F∘T₁Coequalizer ≈⟨ assoc₂ ⟩
    actionˡ' ∘ᵥ α ◁ T₁ ∘ᵥ Coequalizer.arr F∘T₁Coequalizer ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
    actionˡ' ∘ᵥ (α ∘ᵥ Coequalizer.arr F₂⊗F₁) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ (⟺ αSq) ⟩
    actionˡ' ∘ᵥ (Coequalizer.arr F'₂⊗F'₁ ∘ᵥ (α₂ ⊚₁ α₁)) ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
    actionˡ' ∘ᵥ Coequalizer.arr F'₂⊗F'₁ ◁ T₁ ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ sym-assoc₂ ⟩
    (actionˡ' ∘ᵥ Coequalizer.arr F'₂⊗F'₁ ◁ T₁) ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ ⟺ actionˡ'Sq ⟩∘⟨refl ⟩
    (Coequalizer.arr F'₂⊗F'₁ ∘ᵥ F'₂▷actionˡ'₁) ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ assoc₂ ⟩
    Coequalizer.arr F'₂⊗F'₁ ∘ᵥ F'₂▷actionˡ'₁ ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ refl⟩∘⟨ linearˡ-square ⟩
    Coequalizer.arr F'₂⊗F'₁ ∘ᵥ (α₂ ⊚₁ α₁) ∘ᵥ F₂▷actionˡ₁ ≈⟨ sym-assoc₂ ⟩
    (Coequalizer.arr F'₂⊗F'₁ ∘ᵥ (α₂ ⊚₁ α₁)) ∘ᵥ F₂▷actionˡ₁ ≈⟨ αSq ⟩∘⟨refl ⟩
    (α ∘ᵥ Coequalizer.arr F₂⊗F₁) ∘ᵥ F₂▷actionˡ₁ ≈⟨ assoc₂ ⟩
    α ∘ᵥ Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂▷actionˡ₁ ≈⟨ refl⟩∘⟨ actionˡSq ⟩
    α ∘ᵥ actionˡ ∘ᵥ Coequalizer.arr F∘T₁Coequalizer ≈⟨ sym-assoc₂ ⟩
    (α ∘ᵥ actionˡ) ∘ᵥ Coequalizer.arr F∘T₁Coequalizer ∎
    where
      open hom.HomReasoning

  linearˡ : actionˡ' ∘ᵥ α ◁ T₁ ≈ α ∘ᵥ actionˡ
  linearˡ = Coequalizer⇒Epi (hom C₁ C₃) F∘T₁Coequalizer
                            (actionˡ' ∘ᵥ α ◁ T₁) (α ∘ᵥ actionˡ)
                            linearˡ∘arr


  open TensorproductOfBimodules.Right-Action B₂ B₁ using (T₃∘FCoequalizer; actionʳ₂◁F₁; actionʳSq)
  open TensorproductOfBimodules.Right-Action B'₂ B'₁ using () renaming (actionʳ₂◁F₁ to actionʳ'₂◁F'₁; actionʳSq to actionʳ'Sq)

  linearʳ-square : actionʳ'₂◁F'₁ ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈ (α₂ ⊚₁ α₁) ∘ᵥ actionʳ₂◁F₁
  linearʳ-square = begin
    actionʳ'₂◁F'₁ ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ assoc₂ ⟩
    actionʳ'₂ ◁ F'₁ ∘ᵥ associator.to ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ refl⟩∘⟨ α⇐-⊚ ⟩
    actionʳ'₂ ◁ F'₁ ∘ᵥ ((T₃ ▷ α₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
    (actionʳ'₂ ◁ F'₁ ∘ᵥ ((T₃ ▷ α₂) ⊚₁ α₁)) ∘ᵥ associator.to ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
    ((actionʳ'₂ ∘ᵥ T₃ ▷ α₂) ⊚₁ (id₂ ∘ᵥ α₁)) ∘ᵥ associator.to ≈⟨ linearʳ₂ ⟩⊚⟨ identity₂ˡ ⟩∘⟨refl ⟩
    ((α₂ ∘ᵥ actionʳ₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ refl⟩⊚⟨ ⟺ identity₂ʳ ⟩∘⟨refl ⟩
    ((α₂ ∘ᵥ actionʳ₂) ⊚₁ (α₁ ∘ᵥ id₂)) ∘ᵥ associator.to ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
    ((α₂ ⊚₁ α₁) ∘ᵥ actionʳ₂ ◁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
    (α₂ ⊚₁ α₁) ∘ᵥ actionʳ₂◁F₁ ∎
    where
      open hom.HomReasoning

  linearʳ∘arr : (actionʳ' ∘ᵥ T₃ ▷ α) ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ≈ (α ∘ᵥ actionʳ) ∘ᵥ Coequalizer.arr T₃∘FCoequalizer
  linearʳ∘arr = begin
    (actionʳ' ∘ᵥ T₃ ▷ α) ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ≈⟨ assoc₂ ⟩
    actionʳ' ∘ᵥ T₃ ▷ α ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
    actionʳ' ∘ᵥ T₃ ▷ (α ∘ᵥ Coequalizer.arr F₂⊗F₁) ≈⟨ refl⟩∘⟨ ▷-resp-≈ (⟺ αSq) ⟩
    actionʳ' ∘ᵥ T₃ ▷ (Coequalizer.arr F'₂⊗F'₁ ∘ᵥ (α₂ ⊚₁ α₁)) ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩
    actionʳ' ∘ᵥ T₃ ▷ Coequalizer.arr F'₂⊗F'₁ ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ sym-assoc₂ ⟩
    (actionʳ' ∘ᵥ T₃ ▷ Coequalizer.arr F'₂⊗F'₁) ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ ⟺ actionʳ'Sq ⟩∘⟨refl ⟩
    (Coequalizer.arr F'₂⊗F'₁ ∘ᵥ actionʳ'₂◁F'₁) ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ assoc₂ ⟩
    Coequalizer.arr F'₂⊗F'₁ ∘ᵥ actionʳ'₂◁F'₁ ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ refl⟩∘⟨ linearʳ-square ⟩
    Coequalizer.arr F'₂⊗F'₁ ∘ᵥ (α₂ ⊚₁ α₁) ∘ᵥ actionʳ₂◁F₁ ≈⟨ sym-assoc₂ ⟩
    (Coequalizer.arr F'₂⊗F'₁ ∘ᵥ (α₂ ⊚₁ α₁)) ∘ᵥ actionʳ₂◁F₁ ≈⟨ αSq ⟩∘⟨refl ⟩
    (α ∘ᵥ Coequalizer.arr F₂⊗F₁) ∘ᵥ actionʳ₂◁F₁ ≈⟨ assoc₂ ⟩
    α ∘ᵥ Coequalizer.arr F₂⊗F₁ ∘ᵥ actionʳ₂◁F₁ ≈⟨ refl⟩∘⟨ actionʳSq ⟩
    α ∘ᵥ actionʳ ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ≈⟨ sym-assoc₂ ⟩
    (α ∘ᵥ actionʳ) ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ∎
    where
      open hom.HomReasoning

  linearʳ : actionʳ' ∘ᵥ T₃ ▷ α ≈ α ∘ᵥ actionʳ
  linearʳ = Coequalizer⇒Epi (hom C₁ C₃) T₃∘FCoequalizer
                            (actionʳ' ∘ᵥ T₃ ▷ α) (α ∘ᵥ actionʳ)
                            linearʳ∘arr

  h₂⊗h₁ : Bimodulehomomorphism B₂⊗B₁ B'₂⊗B'₁
  h₂⊗h₁ = record
    { α = α
    ; linearˡ = linearˡ
    ; linearʳ = linearʳ
    }
