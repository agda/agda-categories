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
open ComposeWithLocalCoequalizer 𝒞 localCoeq using (_coeq-◁_; _▷-coeq_)

private
  _⊗₀_ = TensorproductOfBimodules.B₂⊗B₁
  _⊗₁_ = TensorproductOfHomomorphisms.h₂⊗h₁

infixr 30 _⊗₀_ _⊗₁_

Id-Bimod : {M : Monad 𝒞} → Bimodule M M
Id-Bimod {M} = id-bimodule M

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞 hiding (triangle)

import Categories.Diagram.Coequalizer
import Categories.Diagram.Coequalizer.Properties
import Categories.Morphism

-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    open Categories.Morphism (hom X Y) public using (_≅_)
    open Categories.Diagram.Coequalizer (hom X Y) public
    open Categories.Diagram.Coequalizer.Properties (hom X Y) public

open HomCat

-- Id-Bimod ⊗₀ B → B --
module Left-Unitor where
  open TensorproductOfBimodules Id-Bimod B using () renaming (F₂⊗F₁ to T₂⊗F)
  open Bimodule B using (F; actionˡ; actionʳ; assoc; assoc-actionʳ) renaming (identityʳ to B-identityʳ)
  open Monad M₁ using () renaming (T to T₁)
  open Monad M₂ using () renaming (T to T₂; η to η₂; μ to μ₂; identityʳ to M₂-identityʳ)

  module 2-cell where
    open TensorproductOfBimodules Id-Bimod B using (act-to-the-left; act-to-the-right)

    {-
    We want to show that the following is a coequalizer: --

                     act-to-the-left              actionʳ
      T₂ ∘₁ T₂ ∘₁ F ==================> T₂ ∘₁ F -----------> F
                     act-to-the-right

    To do so we construct a split coequalizer.
    -}

    section₁ : T₂ ∘₁ F ⇒₂ T₂ ∘₁ T₂ ∘₁ F
    section₁ = η₂ ◁ (T₂ ∘₁ F) ∘ᵥ unitorˡ.to

    section₂ : F ⇒₂ T₂ ∘₁ F
    section₂ = η₂ ◁ F ∘ᵥ unitorˡ.to

    abstract
      actionʳ-eq : actionʳ ∘ᵥ act-to-the-left ≈ actionʳ ∘ᵥ act-to-the-right
      actionʳ-eq = ⟺ assoc-actionʳ
        where
          open hom.HomReasoning

      isSection₁ : act-to-the-right ∘ᵥ section₁ ≈ id₂
      isSection₁ = begin
        (μ₂ ◁ F ∘ᵥ associator.to) ∘ᵥ η₂ ◁ (T₂ ∘₁ F) ∘ᵥ unitorˡ.to ≈⟨ assoc₂ ⟩
        μ₂ ◁ F ∘ᵥ associator.to ∘ᵥ η₂ ◁ (T₂ ∘₁ F) ∘ᵥ unitorˡ.to   ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
        μ₂ ◁ F ∘ᵥ (associator.to ∘ᵥ η₂ ◁ (T₂ ∘₁ F)) ∘ᵥ unitorˡ.to ≈⟨ refl⟩∘⟨ α⇐-◁-∘₁ ⟩∘⟨refl ⟩
        μ₂ ◁ F ∘ᵥ (η₂ ◁ T₂ ◁ F ∘ᵥ associator.to) ∘ᵥ unitorˡ.to    ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        μ₂ ◁ F ∘ᵥ η₂ ◁ T₂ ◁ F ∘ᵥ associator.to ∘ᵥ unitorˡ.to      ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                                      ⟺ unitorˡ-coherence-inv ⟩
        μ₂ ◁ F ∘ᵥ η₂ ◁ T₂ ◁ F ∘ᵥ unitorˡ.to ◁ F                   ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
        μ₂ ◁ F ∘ᵥ (η₂ ◁ T₂ ∘ᵥ unitorˡ.to) ◁ F                     ≈⟨ ∘ᵥ-distr-◁ ⟩
        (μ₂ ∘ᵥ η₂ ◁ T₂ ∘ᵥ unitorˡ.to) ◁ F                         ≈⟨ ◁-resp-≈ M₂-identityʳ ⟩
        id₂ ◁ F                                                   ≈⟨ id₂◁ ⟩
        id₂                                                       ∎
        where
          open hom.HomReasoning

      isSection₂ : actionʳ ∘ᵥ section₂ ≈ id₂
      isSection₂ = B-identityʳ

      sections-compatible : section₂ ∘ᵥ actionʳ ≈ act-to-the-left ∘ᵥ section₁
      sections-compatible = begin
        (η₂ ◁ F ∘ᵥ unitorˡ.to) ∘ᵥ actionʳ              ≈⟨ assoc₂ ⟩
        η₂ ◁ F ∘ᵥ unitorˡ.to ∘ᵥ actionʳ                ≈⟨ refl⟩∘⟨ ⟺ ▷-∘ᵥ-λ⇐ ⟩
        η₂ ◁ F ∘ᵥ id₁ ▷ actionʳ ∘ᵥ unitorˡ.to          ≈⟨ sym-assoc₂ ⟩
        (η₂ ◁ F ∘ᵥ id₁ ▷ actionʳ) ∘ᵥ unitorˡ.to        ≈⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩
        (T₂ ▷ actionʳ ∘ᵥ η₂ ◁ (T₂ ∘₁ F)) ∘ᵥ unitorˡ.to ≈⟨ assoc₂ ⟩
        T₂ ▷ actionʳ ∘ᵥ η₂ ◁ (T₂ ∘₁ F) ∘ᵥ unitorˡ.to   ∎
        where
          open hom.HomReasoning

    -- end abstract --

    FisCoequalizer : IsCoequalizer act-to-the-left act-to-the-right actionʳ
    FisCoequalizer = splitCoequalizer⇒Coequalizer-sym
                       {f = act-to-the-left} {g = act-to-the-right} {e = actionʳ}
                       section₁
                       section₂
                       actionʳ-eq
                       isSection₁
                       isSection₂
                       sections-compatible

    FCoequalizer : Coequalizer act-to-the-left act-to-the-right
    FCoequalizer = IsCoequalizer⇒Coequalizer FisCoequalizer

    Unitorˡ⊗Iso : Bimodule.F (Id-Bimod ⊗₀ B) ≅ F
    Unitorˡ⊗Iso = up-to-iso T₂⊗F FCoequalizer

    λ⇒⊗ : Bimodule.F (Id-Bimod ⊗₀ B) ⇒₂ F
    λ⇒⊗ = _≅_.from Unitorˡ⊗Iso

    triangle : λ⇒⊗ ∘ᵥ Coequalizer.arr T₂⊗F ≈ actionʳ
    triangle = up-to-iso-triangle T₂⊗F FCoequalizer

  open 2-cell using (λ⇒⊗; triangle) public

  module Linear-Left where
    open TensorproductOfBimodules.Left-Action Id-Bimod B
      using () renaming (actionˡSq to actionˡSqT₂⊗F)
    open Bimodule (Id-Bimod ⊗₀ B) using () renaming (actionˡ to actionˡT₂⊗F)

    abstract
      linearˡ∘arr : (actionˡ ∘ᵥ λ⇒⊗ ◁ T₁) ∘ᵥ Coequalizer.arr T₂⊗F ◁ T₁
                    ≈ (λ⇒⊗ ∘ᵥ actionˡT₂⊗F) ∘ᵥ Coequalizer.arr T₂⊗F ◁ T₁
      linearˡ∘arr = begin
        (actionˡ ∘ᵥ λ⇒⊗ ◁ T₁) ∘ᵥ Coequalizer.arr T₂⊗F ◁ T₁ ≈⟨ assoc₂ ⟩
        actionˡ ∘ᵥ λ⇒⊗ ◁ T₁ ∘ᵥ Coequalizer.arr T₂⊗F ◁ T₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
        actionˡ ∘ᵥ (λ⇒⊗ ∘ᵥ Coequalizer.arr T₂⊗F) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ triangle ⟩
        actionˡ ∘ᵥ actionʳ ◁ T₁ ≈⟨ ⟺ assoc ⟩
        actionʳ ∘ᵥ T₂ ▷ actionˡ ∘ᵥ associator.from ≈⟨ ⟺ triangle ⟩∘⟨refl ⟩
        (λ⇒⊗ ∘ᵥ Coequalizer.arr T₂⊗F) ∘ᵥ T₂ ▷ actionˡ ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
        λ⇒⊗ ∘ᵥ Coequalizer.arr T₂⊗F ∘ᵥ T₂ ▷ actionˡ ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ actionˡSqT₂⊗F ⟩
        λ⇒⊗ ∘ᵥ actionˡT₂⊗F ∘ᵥ Coequalizer.arr T₂⊗F ◁ T₁ ≈⟨ sym-assoc₂ ⟩
        (λ⇒⊗ ∘ᵥ actionˡT₂⊗F) ∘ᵥ Coequalizer.arr T₂⊗F ◁ T₁ ∎
        where
          open hom.HomReasoning

      linearˡ : actionˡ ∘ᵥ λ⇒⊗ ◁ T₁ ≈ λ⇒⊗ ∘ᵥ actionˡT₂⊗F
      linearˡ = Coequalizer⇒Epi
                  (T₂⊗F coeq-◁ T₁)
                  (actionˡ ∘ᵥ λ⇒⊗ ◁ T₁)
                  (λ⇒⊗ ∘ᵥ actionˡT₂⊗F)
                  linearˡ∘arr
        where
          open LocalCoequalizers localCoeq
    -- end abstract --


  module Linear-Right where
    open TensorproductOfBimodules.Right-Action Id-Bimod B
      using () renaming (actionʳSq to actionʳSqT₂⊗F)
    open Bimodule (Id-Bimod ⊗₀ B) using () renaming (actionʳ to actionʳT₂⊗F)

    abstract
      linearʳ∘arr : (actionʳ ∘ᵥ T₂ ▷ λ⇒⊗) ∘ᵥ T₂ ▷ Coequalizer.arr T₂⊗F
                    ≈ (λ⇒⊗ ∘ᵥ actionʳT₂⊗F) ∘ᵥ T₂ ▷ Coequalizer.arr T₂⊗F
      linearʳ∘arr = begin
        (actionʳ ∘ᵥ T₂ ▷  λ⇒⊗) ∘ᵥ T₂ ▷ Coequalizer.arr T₂⊗F ≈⟨ assoc₂ ⟩
        actionʳ ∘ᵥ T₂ ▷ λ⇒⊗ ∘ᵥ T₂ ▷ Coequalizer.arr T₂⊗F ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
        actionʳ ∘ᵥ T₂ ▷ (λ⇒⊗ ∘ᵥ Coequalizer.arr T₂⊗F) ≈⟨ refl⟩∘⟨ ▷-resp-≈ triangle ⟩
        actionʳ ∘ᵥ T₂ ▷ actionʳ ≈⟨ ⟺ assoc-actionʳ ⟩
        actionʳ ∘ᵥ μ₂ ◁ F ∘ᵥ associator.to ≈⟨ ⟺ triangle ⟩∘⟨refl ⟩
        (λ⇒⊗ ∘ᵥ Coequalizer.arr T₂⊗F) ∘ᵥ μ₂ ◁ F ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
        λ⇒⊗ ∘ᵥ Coequalizer.arr T₂⊗F ∘ᵥ μ₂ ◁ F ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ actionʳSqT₂⊗F ⟩
        λ⇒⊗ ∘ᵥ actionʳT₂⊗F ∘ᵥ T₂ ▷ Coequalizer.arr T₂⊗F ≈⟨ sym-assoc₂ ⟩
        (λ⇒⊗ ∘ᵥ actionʳT₂⊗F) ∘ᵥ T₂ ▷ Coequalizer.arr T₂⊗F ∎
        where
          open hom.HomReasoning

      linearʳ : actionʳ ∘ᵥ T₂ ▷ λ⇒⊗ ≈ λ⇒⊗ ∘ᵥ actionʳT₂⊗F
      linearʳ = Coequalizer⇒Epi
                  (T₂ ▷-coeq T₂⊗F)
                  (actionʳ ∘ᵥ T₂ ▷ λ⇒⊗)
                  (λ⇒⊗ ∘ᵥ actionʳT₂⊗F)
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

  open import Categories.Category.Construction.Bimodules
    renaming (Bimodules to Bimodules₁)
  open import Categories.Category.Construction.Bimodules.Properties

  Unitorˡ⊗ : Categories.Morphism._≅_ (Bimodules₁ M₁ M₂) (Id-Bimod ⊗₀ B) B
  Unitorˡ⊗ = αisIso⇒Iso Unitorˡ⊗From λ⇒⊗isIso
    where
      open Monad M₁ using () renaming (C to C₁)
      open Monad M₂ using () renaming (C to C₂)
      open Bimodule-Isomorphism using (αisIso⇒Iso)
      λ⇒⊗isIso : Categories.Morphism.IsIso (hom C₁ C₂) λ⇒⊗
      λ⇒⊗isIso = record
       { inv = _≅_.to 2-cell.Unitorˡ⊗Iso
       ; iso = _≅_.iso 2-cell.Unitorˡ⊗Iso
       }


-- Id-Bimod ⊗₀ B → B --
module Right-Unitor where
  open TensorproductOfBimodules B Id-Bimod using () renaming (F₂⊗F₁ to F⊗T₁)
  open Bimodule B using (F; actionˡ; actionʳ; sym-assoc; assoc-actionˡ; sym-assoc-actionˡ) renaming (identityˡ to B-identityˡ)
  open Monad M₁ using () renaming (T to T₁; η to η₁; μ to μ₁; identityˡ to M₁-identityˡ)
  open Monad M₂ using () renaming (T to T₂)

  module 2-cell where
    open TensorproductOfBimodules B Id-Bimod using (act-to-the-left; act-to-the-right)

    {-
    We want to show that the following is a coequalizer: --

                     act-to-the-left              actionˡ
      F ∘₁ T₁ ∘₁ T₁ ==================> F ∘₁ T₁ -----------> F
                     act-to-the-right

    To do so we construct a split coequalizer.
    -}

    section₁ : F ∘₁ T₁ ⇒₂ F ∘₁ T₁ ∘₁ T₁
    section₁ = F ▷ T₁ ▷ η₁ ∘ᵥ F ▷ unitorʳ.to

    section₂ : F ⇒₂ F ∘₁ T₁
    section₂ = F ▷ η₁ ∘ᵥ unitorʳ.to

    abstract
      actionˡ-eq : actionˡ ∘ᵥ act-to-the-left ≈ actionˡ ∘ᵥ act-to-the-right
      actionˡ-eq = ⟺ sym-assoc-actionˡ
        where
          open hom.HomReasoning

      isSection₁ : act-to-the-left ∘ᵥ section₁ ≈ id₂
      isSection₁ = begin
        F ▷ μ₁ ∘ᵥ F ▷ T₁ ▷ η₁ ∘ᵥ F ▷ unitorʳ.to ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
        F ▷ μ₁ ∘ᵥ F ▷ (T₁ ▷ η₁ ∘ᵥ unitorʳ.to)   ≈⟨ ∘ᵥ-distr-▷ ⟩
        F ▷ (μ₁ ∘ᵥ T₁ ▷ η₁ ∘ᵥ unitorʳ.to)       ≈⟨ ▷-resp-≈ M₁-identityˡ ⟩
        F ▷ id₂                                 ≈⟨ ▷id₂ ⟩
        id₂                                     ∎
        where
          open hom.HomReasoning

      isSection₂ : actionˡ ∘ᵥ section₂ ≈ id₂
      isSection₂ = B-identityˡ

      sections-compatible : section₂ ∘ᵥ actionˡ ≈ act-to-the-right ∘ᵥ section₁
      sections-compatible = begin
        (F ▷ η₁ ∘ᵥ unitorʳ.to) ∘ᵥ actionˡ                                   ≈⟨ assoc₂ ⟩
        F ▷ η₁ ∘ᵥ unitorʳ.to ∘ᵥ actionˡ                                     ≈⟨ refl⟩∘⟨ ⟺ ◁-∘ᵥ-ρ⇐ ⟩
        F ▷ η₁ ∘ᵥ actionˡ ◁ id₁ ∘ᵥ unitorʳ.to                               ≈⟨ sym-assoc₂ ⟩
        (F ▷ η₁ ∘ᵥ actionˡ ◁ id₁) ∘ᵥ unitorʳ.to                             ≈⟨ ◁-▷-exchg ⟩∘⟨refl ⟩
        (actionˡ ◁ T₁ ∘ᵥ (F ∘₁ T₁) ▷ η₁) ∘ᵥ unitorʳ.to                      ≈⟨ assoc₂ ⟩
        actionˡ ◁ T₁ ∘ᵥ (F ∘₁ T₁) ▷ η₁ ∘ᵥ unitorʳ.to                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                                               ⟺ unitorʳ-coherence-inv ⟩
        actionˡ ◁ T₁ ∘ᵥ (F ∘₁ T₁) ▷ η₁ ∘ᵥ associator.to ∘ᵥ F ▷ unitorʳ.to   ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
        actionˡ ◁ T₁ ∘ᵥ ((F ∘₁ T₁) ▷ η₁ ∘ᵥ associator.to) ∘ᵥ F ▷ unitorʳ.to ≈⟨ refl⟩∘⟨ ⟺ α⇐-▷-∘₁ ⟩∘⟨refl ⟩
        actionˡ ◁ T₁ ∘ᵥ (associator.to ∘ᵥ F ▷ T₁ ▷ η₁) ∘ᵥ F ▷ unitorʳ.to    ≈⟨ refl⟩∘⟨ assoc₂ ⟩
        actionˡ ◁ T₁ ∘ᵥ associator.to ∘ᵥ F ▷ T₁ ▷ η₁ ∘ᵥ F ▷ unitorʳ.to      ≈⟨ sym-assoc₂ ⟩
        (actionˡ ◁ T₁ ∘ᵥ associator.to) ∘ᵥ F ▷ T₁ ▷ η₁ ∘ᵥ F ▷ unitorʳ.to    ∎
        where
          open hom.HomReasoning
    -- end abstract --

    FisCoequalizer : IsCoequalizer act-to-the-left act-to-the-right actionˡ
    FisCoequalizer = splitCoequalizer⇒Coequalizer
                       {f = act-to-the-left} {g = act-to-the-right} {e = actionˡ}
                       section₁
                       section₂
                       actionˡ-eq
                       isSection₁
                       isSection₂
                       sections-compatible

    FCoequalizer : Coequalizer act-to-the-left act-to-the-right
    FCoequalizer = IsCoequalizer⇒Coequalizer FisCoequalizer

    Unitorʳ⊗Iso : Bimodule.F (B ⊗₀ Id-Bimod) ≅ F
    Unitorʳ⊗Iso = up-to-iso F⊗T₁ FCoequalizer

    ρ⇒⊗ : Bimodule.F (B ⊗₀ Id-Bimod) ⇒₂ F
    ρ⇒⊗ = _≅_.from Unitorʳ⊗Iso

    triangle : ρ⇒⊗ ∘ᵥ Coequalizer.arr F⊗T₁ ≈ actionˡ
    triangle = up-to-iso-triangle F⊗T₁ FCoequalizer

  open 2-cell using (ρ⇒⊗; triangle) public

  module Linear-Left where
    open TensorproductOfBimodules.Left-Action B Id-Bimod
      using () renaming (actionˡSq to actionˡSqF⊗T₁)
    open Bimodule (B ⊗₀ Id-Bimod) using () renaming (actionˡ to actionˡF⊗T₁)

    abstract
      linearˡ∘arr : (actionˡ ∘ᵥ ρ⇒⊗ ◁ T₁) ∘ᵥ Coequalizer.arr F⊗T₁ ◁ T₁
                    ≈ (ρ⇒⊗ ∘ᵥ actionˡF⊗T₁) ∘ᵥ Coequalizer.arr F⊗T₁ ◁ T₁
      linearˡ∘arr = begin
        (actionˡ ∘ᵥ ρ⇒⊗ ◁ T₁) ∘ᵥ Coequalizer.arr F⊗T₁ ◁ T₁ ≈⟨ assoc₂ ⟩
        actionˡ ∘ᵥ ρ⇒⊗ ◁ T₁ ∘ᵥ Coequalizer.arr F⊗T₁ ◁ T₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
        actionˡ ∘ᵥ (ρ⇒⊗ ∘ᵥ Coequalizer.arr F⊗T₁) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ triangle ⟩
        actionˡ ∘ᵥ actionˡ ◁ T₁ ≈⟨ ⟺ assoc-actionˡ ⟩
        actionˡ ∘ᵥ F ▷ μ₁ ∘ᵥ associator.from ≈⟨ ⟺ triangle ⟩∘⟨refl ⟩
        (ρ⇒⊗ ∘ᵥ Coequalizer.arr F⊗T₁) ∘ᵥ F ▷ μ₁ ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
        ρ⇒⊗ ∘ᵥ Coequalizer.arr F⊗T₁ ∘ᵥ F ▷ μ₁ ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ actionˡSqF⊗T₁ ⟩
        ρ⇒⊗ ∘ᵥ actionˡF⊗T₁ ∘ᵥ Coequalizer.arr F⊗T₁ ◁ T₁ ≈⟨ sym-assoc₂ ⟩
        (ρ⇒⊗ ∘ᵥ actionˡF⊗T₁) ∘ᵥ Coequalizer.arr F⊗T₁ ◁ T₁ ∎
        where
          open hom.HomReasoning

      linearˡ : actionˡ ∘ᵥ ρ⇒⊗ ◁ T₁ ≈ ρ⇒⊗ ∘ᵥ actionˡF⊗T₁
      linearˡ = Coequalizer⇒Epi
                  (F⊗T₁ coeq-◁ T₁)
                  (actionˡ ∘ᵥ ρ⇒⊗ ◁ T₁)
                  (ρ⇒⊗ ∘ᵥ actionˡF⊗T₁)
                  linearˡ∘arr
        where
          open LocalCoequalizers localCoeq
    -- end abstract --

  module Linear-Right where
    open TensorproductOfBimodules.Right-Action B Id-Bimod
      using () renaming (actionʳSq to actionʳSqF⊗T₁)
    open Bimodule (B ⊗₀ Id-Bimod) using () renaming (actionʳ to actionʳF⊗T₁)

    abstract
      linearʳ∘arr : (actionʳ ∘ᵥ T₂ ▷ ρ⇒⊗) ∘ᵥ T₂ ▷ Coequalizer.arr F⊗T₁
                    ≈ (ρ⇒⊗ ∘ᵥ actionʳF⊗T₁) ∘ᵥ T₂ ▷ Coequalizer.arr F⊗T₁
      linearʳ∘arr = begin
        (actionʳ ∘ᵥ T₂ ▷ ρ⇒⊗) ∘ᵥ T₂ ▷ Coequalizer.arr F⊗T₁ ≈⟨ assoc₂ ⟩
        actionʳ ∘ᵥ T₂ ▷ ρ⇒⊗ ∘ᵥ T₂ ▷ Coequalizer.arr F⊗T₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
        actionʳ ∘ᵥ T₂ ▷ (ρ⇒⊗ ∘ᵥ Coequalizer.arr F⊗T₁) ≈⟨ refl⟩∘⟨ ▷-resp-≈ triangle ⟩
        actionʳ ∘ᵥ T₂ ▷ actionˡ ≈⟨ ⟺ sym-assoc ⟩
        actionˡ ∘ᵥ actionʳ ◁ T₁ ∘ᵥ associator.to ≈⟨ ⟺ triangle ⟩∘⟨refl ⟩
        (ρ⇒⊗ ∘ᵥ Coequalizer.arr F⊗T₁) ∘ᵥ actionʳ ◁ T₁ ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
        ρ⇒⊗ ∘ᵥ Coequalizer.arr F⊗T₁ ∘ᵥ actionʳ ◁ T₁ ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ actionʳSqF⊗T₁ ⟩
        ρ⇒⊗ ∘ᵥ actionʳF⊗T₁ ∘ᵥ T₂ ▷ Coequalizer.arr F⊗T₁ ≈⟨ sym-assoc₂ ⟩
        (ρ⇒⊗ ∘ᵥ actionʳF⊗T₁) ∘ᵥ T₂ ▷ Coequalizer.arr F⊗T₁ ∎
        where
          open hom.HomReasoning

      linearʳ : actionʳ ∘ᵥ T₂ ▷ ρ⇒⊗ ≈ ρ⇒⊗ ∘ᵥ actionʳF⊗T₁
      linearʳ = Coequalizer⇒Epi
                  (T₂ ▷-coeq F⊗T₁)
                  (actionʳ ∘ᵥ T₂ ▷ ρ⇒⊗)
                  (ρ⇒⊗ ∘ᵥ actionʳF⊗T₁)
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

  open import Categories.Category.Construction.Bimodules
    renaming (Bimodules to Bimodules₁)
  open import Categories.Category.Construction.Bimodules.Properties

  Unitorʳ⊗ : Categories.Morphism._≅_ (Bimodules₁ M₁ M₂) (B ⊗₀ Id-Bimod) B
  Unitorʳ⊗ = αisIso⇒Iso Unitorʳ⊗From ρ⇒⊗isIso
    where
      open Monad M₁ using () renaming (C to C₁)
      open Monad M₂ using () renaming (C to C₂)
      open Bimodule-Isomorphism using (αisIso⇒Iso)
      ρ⇒⊗isIso : Categories.Morphism.IsIso (hom C₁ C₂) ρ⇒⊗
      ρ⇒⊗isIso = record
       { inv = _≅_.to 2-cell.Unitorʳ⊗Iso
       ; iso = _≅_.iso 2-cell.Unitorʳ⊗Iso
       }
