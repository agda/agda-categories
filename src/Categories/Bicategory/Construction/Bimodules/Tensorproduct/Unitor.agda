{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule


-- We will define the left- and right-unitor in the bicategory of monads and bimodules. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Unitor
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞}
  {M₁ M₂ : Monad 𝒞} {B : Bimodule M₁ M₂} where

open import Categories.Bicategory.Monad.Bimodule.Homomorphism using (Bimodulehomomorphism)

import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} as TensorproductOfBimodules
import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq} as TensorproductOfHomomorphisms
open TensorproductOfBimodules using (CoeqBimods) renaming (Tensorproduct to infixr 30 _⊗₀_)
open TensorproductOfHomomorphisms using () renaming (Tensorproduct to infixr 30 _⊗₁_)

open ComposeWithLocalCoequalizer 𝒞 localCoeq using (_coeq-◁_; _▷-coeq_)

Id-Bimod : {M : Monad 𝒞} → Bimodule M M
Id-Bimod {M} = id-bimodule M

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞 hiding (triangle)
open Shorthands

open Monad using (C; T; η; μ; identityʳ; identityˡ)
open Bimodule using (F; actionˡ; actionʳ; assoc; sym-assoc; assoc-actionʳ; assoc-actionˡ; sym-assoc-actionˡ; identityʳ; identityˡ)
-- We oveload the names identityʳ and identityˡ. Agda is able to resolve the resulting conflicts. --

open import Categories.Category.Construction.Bimodules using () renaming (Bimodules to Bimodules₁)
import Categories.Category.Construction.Bimodules.Properties

import Categories.Morphism.Reasoning
open import Categories.Morphism (hom (C M₁) (C M₂)) using (IsIso)
open import Categories.Diagram.Coequalizer (hom (C M₁) (C M₂))
open import Categories.Diagram.Coequalizer.Properties (hom (C M₁) (C M₂))

open import Categories.Category using (Category)

-- To get equivalence of object with the category as an implicit parameter into scope --
module Equivalence {a} {b} {c} {C : Category a b c} where
  open import Categories.Morphism C using (_≅_) public

open Equivalence

-- Id-Bimod ⊗₀ B ⇒ B --
module Left-Unitor where

  module 2-cell where
    open TensorproductOfBimodules Id-Bimod B using (act-to-the-left; act-to-the-right)

    {-
    We want to show that the following is a coequalizer: --

                           act-to-the-left                  actionʳ
      T M₂ ∘₁ T M₂ ∘₁ F B ==================> T M₂ ∘₁ F B -----------> F B
                           act-to-the-right

    To do so we construct a split coequalizer.
    -}

    section₁ : T M₂ ∘₁ F B ⇒₂ T M₂ ∘₁ T M₂ ∘₁ F B
    section₁ = η M₂ ◁ (T M₂ ∘₁ F B) ∘ᵥ λ⇐

    section₂ : F B ⇒₂ T M₂ ∘₁ F B
    section₂ = η M₂ ◁ F B ∘ᵥ λ⇐

    abstract
      actionʳ-eq : actionʳ B ∘ᵥ act-to-the-left ≈ actionʳ B ∘ᵥ act-to-the-right
      actionʳ-eq = ⟺ (assoc-actionʳ B)
        where
          open hom.HomReasoning

      isSection₁ : act-to-the-right ∘ᵥ section₁ ≈ id₂
      isSection₁ = begin
        (μ M₂ ◁ F B ∘ᵥ α⇐) ∘ᵥ η M₂ ◁ (T M₂ ∘₁ F B) ∘ᵥ λ⇐ ≈⟨ assoc²γδ ⟩
        μ M₂ ◁ F B ∘ᵥ (α⇐ ∘ᵥ η M₂ ◁ (T M₂ ∘₁ F B)) ∘ᵥ λ⇐ ≈⟨ refl⟩∘⟨ pushˡ α⇐-◁-∘₁ ⟩
        μ M₂ ◁ F B ∘ᵥ η M₂ ◁ T M₂ ◁ F B ∘ᵥ α⇐ ∘ᵥ λ⇐      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ unitorˡ-coherence-inv ⟩
        μ M₂ ◁ F B ∘ᵥ η M₂ ◁ T M₂ ◁ F B ∘ᵥ λ⇐ ◁ F B      ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
        μ M₂ ◁ F B ∘ᵥ (η M₂ ◁ T M₂ ∘ᵥ λ⇐) ◁ F B          ≈⟨ ∘ᵥ-distr-◁ ⟩
        (μ M₂ ∘ᵥ η M₂ ◁ T M₂ ∘ᵥ λ⇐) ◁ F B                ≈⟨ ◁-resp-≈ (identityʳ M₂) ⟩
        id₂ ◁ F B                                        ≈⟨ id₂◁ ⟩
        id₂                                              ∎
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₂)) using (assoc²γδ; pushˡ)

      isSection₂ : actionʳ B ∘ᵥ section₂ ≈ id₂
      isSection₂ = identityʳ B

      sections-compatible : section₂ ∘ᵥ actionʳ B ≈ act-to-the-left ∘ᵥ section₁
      sections-compatible =  ⟺ (glue′ ◁-▷-exchg ▷-∘ᵥ-λ⇐)
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₂)) using (glue′)

    -- end abstract --

    FisCoequalizer : IsCoequalizer act-to-the-left act-to-the-right (actionʳ B)
    FisCoequalizer = splitCoequalizer⇒Coequalizer-sym
                       {f = act-to-the-left} {g = act-to-the-right} {e = actionʳ B}
                       section₁
                       section₂
                       actionʳ-eq
                       isSection₁
                       isSection₂
                       sections-compatible

    FCoequalizer : Coequalizer act-to-the-left act-to-the-right
    FCoequalizer = IsCoequalizer⇒Coequalizer FisCoequalizer

    Unitorˡ⊗Iso : F (Id-Bimod ⊗₀ B) ≅ F B
    Unitorˡ⊗Iso = up-to-iso (CoeqBimods Id-Bimod B) FCoequalizer

    λ⇒⊗ : F (Id-Bimod ⊗₀ B) ⇒₂ F B
    λ⇒⊗ = _≅_.from Unitorˡ⊗Iso

    triangle : λ⇒⊗ ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B) ≈ actionʳ B
    triangle = up-to-iso-triangle (CoeqBimods Id-Bimod B) FCoequalizer

  open 2-cell using (λ⇒⊗; triangle) public

  module Linear-Left where

    abstract
      linearˡ∘arr : (actionˡ B ∘ᵥ λ⇒⊗ ◁ T M₁) ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B) ◁ T M₁
                  ≈ (λ⇒⊗ ∘ᵥ actionˡ (Id-Bimod ⊗₀ B)) ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B) ◁ T M₁
      linearˡ∘arr = begin
        (actionˡ B ∘ᵥ λ⇒⊗ ◁ T M₁) ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B) ◁ T M₁        ≈⟨ glue◽▹ (⟺ (assoc B)) (◁-resp-tri triangle) ⟩
        actionʳ B ∘ᵥ actionˡ-∘                                                             ≈⟨ ⟺ (glue◃◽ triangle (⟺ actionˡSq-⊗)) ⟩
        (λ⇒⊗ ∘ᵥ actionˡ (Id-Bimod ⊗₀ B)) ∘ᵥ Coequalizer.arr (CoeqBimods Id-Bimod B) ◁ T M₁ ∎
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₂)) using (glue◃◽; glue◽▹)
          open TensorproductOfBimodules.Left-Action Id-Bimod B using (actionˡSq-⊗; actionˡ-∘)
          -- actionˡ-∘ = T M₂ ▷ actionˡ B ∘ᵥ α⇒ --

      linearˡ : actionˡ B ∘ᵥ λ⇒⊗ ◁ T M₁ ≈ λ⇒⊗ ∘ᵥ actionˡ (Id-Bimod ⊗₀ B)
      linearˡ = Coequalizer⇒Epi
                  ((CoeqBimods Id-Bimod B) coeq-◁ T M₁)
                  (actionˡ B ∘ᵥ λ⇒⊗ ◁ T M₁)
                  (λ⇒⊗ ∘ᵥ actionˡ (Id-Bimod ⊗₀ B))
                  linearˡ∘arr
        where
          open LocalCoequalizers localCoeq
    -- end abstract --


  module Linear-Right where

    abstract
      linearʳ∘arr : (actionʳ B ∘ᵥ T M₂ ▷ λ⇒⊗) ∘ᵥ T M₂ ▷ Coequalizer.arr (CoeqBimods Id-Bimod B)
                  ≈ (λ⇒⊗ ∘ᵥ actionʳ (Id-Bimod ⊗₀ B)) ∘ᵥ T M₂ ▷ Coequalizer.arr (CoeqBimods Id-Bimod B)
      linearʳ∘arr = begin
        (actionʳ B ∘ᵥ T M₂ ▷  λ⇒⊗) ∘ᵥ T M₂ ▷ Coequalizer.arr (CoeqBimods Id-Bimod B) ≈⟨ glue◽▹ (⟺ (assoc-actionʳ B)) (▷-resp-tri triangle) ⟩
        actionʳ B ∘ᵥ actionʳ-∘                                                       ≈⟨ ⟺ (glue◃◽ triangle (⟺ actionʳSq-⊗)) ⟩
        (λ⇒⊗ ∘ᵥ actionʳ (Id-Bimod ⊗₀ B)) ∘ᵥ T M₂ ▷ Coequalizer.arr (CoeqBimods Id-Bimod B) ∎
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₂)) using (glue◃◽; glue◽▹)
          open TensorproductOfBimodules.Right-Action Id-Bimod B using (actionʳSq-⊗; actionʳ-∘)
          -- actionʳ-∘ = μ M₂ ◁ F B ∘ᵥ α⇐ --

      linearʳ : actionʳ B ∘ᵥ T M₂ ▷ λ⇒⊗ ≈ λ⇒⊗ ∘ᵥ actionʳ (Id-Bimod ⊗₀ B)
      linearʳ = Coequalizer⇒Epi
                  (T M₂ ▷-coeq (CoeqBimods Id-Bimod B))
                  (actionʳ B ∘ᵥ T M₂ ▷ λ⇒⊗)
                  (λ⇒⊗ ∘ᵥ actionʳ (Id-Bimod ⊗₀ B))
                  linearʳ∘arr
        where
          open LocalCoequalizers localCoeq
    -- end abstract --
    

  Unitorˡ⊗From : Bimodulehomomorphism (Id-Bimod ⊗₀ B) B
  Unitorˡ⊗From = record
    { α = λ⇒⊗
    ; linearˡ = Linear-Left.linearˡ
    ; linearʳ = Linear-Right.linearʳ
    }

  Unitorˡ⊗ : Id-Bimod ⊗₀ B ≅ B
  Unitorˡ⊗ = αisIso⇒Iso Unitorˡ⊗From λ⇒⊗isIso
    where
      open Categories.Category.Construction.Bimodules.Properties.Bimodule-Isomorphism using (αisIso⇒Iso)
      λ⇒⊗isIso : IsIso λ⇒⊗
      λ⇒⊗isIso = record
       { inv = _≅_.to 2-cell.Unitorˡ⊗Iso
       ; iso = _≅_.iso 2-cell.Unitorˡ⊗Iso
       }


-- Id-Bimod ⊗₀ B → B --
module Right-Unitor where

  module 2-cell where
    open TensorproductOfBimodules B Id-Bimod using (act-to-the-left; act-to-the-right)

    {-
    We want to show that the following is a coequalizer: --

                           act-to-the-left                  actionˡ
      F B ∘₁ T M₂ ∘₁ T M₂ ==================> F B ∘₁ T M₂ -----------> F B
                           act-to-the-right

    To do so we construct a split coequalizer.
    -}

    section₁ : F B ∘₁ T M₁ ⇒₂ F B ∘₁ T M₁ ∘₁ T M₁
    section₁ = F B ▷ T M₁ ▷ η M₁ ∘ᵥ F B ▷ ρ⇐

    section₂ : F B ⇒₂ F B ∘₁ T M₁
    section₂ = F B ▷ η M₁ ∘ᵥ ρ⇐

    abstract
      actionˡ-eq : actionˡ B ∘ᵥ act-to-the-left ≈ actionˡ B ∘ᵥ act-to-the-right
      actionˡ-eq = ⟺ (sym-assoc-actionˡ B)
        where
          open hom.HomReasoning

      isSection₁ : act-to-the-left ∘ᵥ section₁ ≈ id₂
      isSection₁ = begin
        F B ▷ μ M₁ ∘ᵥ F B ▷ T M₁ ▷ η M₁ ∘ᵥ F B ▷ ρ⇐ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
        F B ▷ μ M₁ ∘ᵥ F B ▷ (T M₁ ▷ η M₁ ∘ᵥ ρ⇐)     ≈⟨ ∘ᵥ-distr-▷ ⟩
        F B ▷ (μ M₁ ∘ᵥ T M₁ ▷ η M₁ ∘ᵥ ρ⇐)           ≈⟨ ▷-resp-≈ (identityˡ M₁) ⟩
        F B ▷ id₂                                   ≈⟨ ▷id₂ ⟩
        id₂                                         ∎
        where
          open hom.HomReasoning

      isSection₂ : actionˡ B ∘ᵥ section₂ ≈ id₂
      isSection₂ = identityˡ B

      sections-compatible : section₂ ∘ᵥ actionˡ B ≈ act-to-the-right ∘ᵥ section₁
      sections-compatible = glue
                              (glue′ ◁-▷-exchg (⟺ α⇐-▷-∘₁))
                              (glue◽▹′ (⟺ ◁-∘ᵥ-ρ⇐) (⟺ unitorʳ-coherence-inv))
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₂)) using (glue; glue′; glue◽▹′)
    -- end abstract --

    FisCoequalizer : IsCoequalizer act-to-the-left act-to-the-right (actionˡ B)
    FisCoequalizer = splitCoequalizer⇒Coequalizer
                       {f = act-to-the-left} {g = act-to-the-right} {e = actionˡ B}
                       section₁
                       section₂
                       actionˡ-eq
                       isSection₁
                       isSection₂
                       sections-compatible

    FCoequalizer : Coequalizer act-to-the-left act-to-the-right
    FCoequalizer = IsCoequalizer⇒Coequalizer FisCoequalizer

    Unitorʳ⊗Iso : F (B ⊗₀ Id-Bimod) ≅ F B
    Unitorʳ⊗Iso = up-to-iso (CoeqBimods B Id-Bimod) FCoequalizer

    ρ⇒⊗ : F (B ⊗₀ Id-Bimod) ⇒₂ F B
    ρ⇒⊗ = _≅_.from Unitorʳ⊗Iso

    triangle : ρ⇒⊗ ∘ᵥ Coequalizer.arr (CoeqBimods B Id-Bimod) ≈ actionˡ B
    triangle = up-to-iso-triangle (CoeqBimods B Id-Bimod) FCoequalizer

  open 2-cell using (ρ⇒⊗; triangle) public

  module Linear-Left where

    abstract
      linearˡ∘arr : (actionˡ B ∘ᵥ ρ⇒⊗ ◁ T M₁) ∘ᵥ Coequalizer.arr (CoeqBimods B Id-Bimod) ◁ T M₁
                  ≈ (ρ⇒⊗ ∘ᵥ actionˡ (B ⊗₀ Id-Bimod)) ∘ᵥ Coequalizer.arr (CoeqBimods B Id-Bimod) ◁ T M₁
      linearˡ∘arr = begin
        (actionˡ B ∘ᵥ ρ⇒⊗ ◁ T M₁) ∘ᵥ Coequalizer.arr (CoeqBimods B Id-Bimod) ◁ T M₁        ≈⟨ glue◽▹ (⟺ (assoc-actionˡ B)) (◁-resp-tri triangle) ⟩
        actionˡ B ∘ᵥ actionˡ-∘                                                             ≈⟨ ⟺ (glue◃◽ triangle (⟺ actionˡSq-⊗)) ⟩
        (ρ⇒⊗ ∘ᵥ actionˡ (B ⊗₀ Id-Bimod)) ∘ᵥ Coequalizer.arr (CoeqBimods B Id-Bimod) ◁ T M₁ ∎
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₂)) using (glue◃◽; glue◽▹)
          open TensorproductOfBimodules.Left-Action B Id-Bimod using (actionˡSq-⊗; actionˡ-∘)
          -- actionˡ-∘ = F B ▷ μ M₁ ∘ᵥ α⇒ --

      linearˡ : actionˡ B ∘ᵥ ρ⇒⊗ ◁ T M₁ ≈ ρ⇒⊗ ∘ᵥ actionˡ (B ⊗₀ Id-Bimod)
      linearˡ = Coequalizer⇒Epi
                  ((CoeqBimods B Id-Bimod) coeq-◁ T M₁)
                  (actionˡ B ∘ᵥ ρ⇒⊗ ◁ T M₁)
                  (ρ⇒⊗ ∘ᵥ actionˡ (B ⊗₀ Id-Bimod))
                  linearˡ∘arr
        where
          open LocalCoequalizers localCoeq
    -- end abstract --

  module Linear-Right where

    abstract
      linearʳ∘arr : (actionʳ B ∘ᵥ T M₂ ▷ ρ⇒⊗) ∘ᵥ T M₂ ▷ Coequalizer.arr (CoeqBimods B Id-Bimod)
                  ≈ (ρ⇒⊗ ∘ᵥ actionʳ (B ⊗₀ Id-Bimod)) ∘ᵥ T M₂ ▷ Coequalizer.arr (CoeqBimods B Id-Bimod)
      linearʳ∘arr = begin
        (actionʳ B ∘ᵥ T M₂ ▷ ρ⇒⊗) ∘ᵥ T M₂ ▷ Coequalizer.arr (CoeqBimods B Id-Bimod)        ≈⟨ glue◽▹ (⟺ (sym-assoc B)) (▷-resp-tri triangle) ⟩
        actionˡ B ∘ᵥ actionʳ-∘                                                             ≈⟨ ⟺ (glue◃◽ triangle (⟺ actionʳSq-⊗)) ⟩
        (ρ⇒⊗ ∘ᵥ actionʳ (B ⊗₀ Id-Bimod)) ∘ᵥ T M₂ ▷ Coequalizer.arr (CoeqBimods B Id-Bimod) ∎
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₂)) using (glue◃◽; glue◽▹)
          open TensorproductOfBimodules.Right-Action B Id-Bimod using (actionʳSq-⊗; actionʳ-∘)
          -- actionʳ-∘ = actionʳ B ◁ T M₁ ∘ᵥ α⇐ --

      linearʳ : actionʳ B ∘ᵥ T M₂ ▷ ρ⇒⊗ ≈ ρ⇒⊗ ∘ᵥ actionʳ (B ⊗₀ Id-Bimod)
      linearʳ = Coequalizer⇒Epi
                  (T M₂ ▷-coeq (CoeqBimods B Id-Bimod))
                  (actionʳ B ∘ᵥ T M₂ ▷ ρ⇒⊗)
                  (ρ⇒⊗ ∘ᵥ actionʳ (B ⊗₀ Id-Bimod))
                  linearʳ∘arr
        where
          open LocalCoequalizers localCoeq
    -- end abstract --
    

  Unitorʳ⊗From : Bimodulehomomorphism (B ⊗₀ Id-Bimod) B
  Unitorʳ⊗From = record
    { α = ρ⇒⊗
    ; linearˡ = Linear-Left.linearˡ
    ; linearʳ = Linear-Right.linearʳ
    }

  Unitorʳ⊗ : B ⊗₀ Id-Bimod ≅ B
  Unitorʳ⊗ = αisIso⇒Iso Unitorʳ⊗From ρ⇒⊗isIso
    where
      open Categories.Category.Construction.Bimodules.Properties.Bimodule-Isomorphism using (αisIso⇒Iso)
      ρ⇒⊗isIso : IsIso ρ⇒⊗
      ρ⇒⊗isIso = record
       { inv = _≅_.to 2-cell.Unitorʳ⊗Iso
       ; iso = _≅_.iso 2-cell.Unitorʳ⊗Iso
       }
