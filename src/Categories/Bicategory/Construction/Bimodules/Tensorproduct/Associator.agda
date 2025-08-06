{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule


-- We will define the associator in the bicategory of monads and bimodules. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ M₄ : Monad 𝒞}
  {B₃ : Bimodule M₃ M₄} {B₂ : Bimodule M₂ M₃} {B₁ : Bimodule M₁ M₂} where

open import Categories.Bicategory.Monad.Bimodule.Homomorphism
import Categories.Bicategory.LocalCoequalizers
open ComposeWithLocalCoequalizer 𝒞 localCoeq

import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} as TensorproductOfBimodules
import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq} as TensorproductOfHomomorphisms
open TensorproductOfBimodules using () renaming (Tensorproduct to infixr 30 _⊗₀_)
open TensorproductOfHomomorphisms using () renaming (Tensorproduct to infixr 30 _⊗₁_)

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands
import Categories.Diagram.Coequalizer
import Categories.Diagram.Coequalizer.Properties
import Categories.Morphism
import Categories.Category
import Categories.Category.Construction.Core


-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    open Categories.Morphism (hom X Y) using (_≅_) public
    open Categories.Category.Definitions (hom X Y) using (CommutativeSquare) public
    open Categories.Category.Construction.Core.Shorthands (hom X Y) using (_∘ᵢ_; _⁻¹) public
    open Categories.Diagram.Coequalizer (hom X Y) using (Coequalizer) public
    open Coequalizer using (obj; arr) public

open HomCat


open Monad using (C; T)
open Bimodule using (F; actionˡ; actionʳ)
open TensorproductOfBimodules using (CoeqBimods; act-to-the-left; act-to-the-right)


-- The associator is a bimodule. We start by constructing its underlying 2-cell. --
module 2-cell where

  -- We want to use that coequalizers commute with coeuqalizers --
  -- c.f. Categories.Diagram.Coequalizer.Properties.CoequalizerOfCoequalizer --
  -- To apply afformentioned module we need to define the appropriate diagram --
  -- Note that we need to plug in the associators of 𝒞 at the apropriate points to define the diagram --
  {-
        f₁₂
     X ====> Y ----> coeqᶠ
     ||      ||       ||
  g₁₂||   h₁₂||  sqᶠⁱ ||
     vv i₁₂  vv       vv        t
     Z ====> W ----> coeqⁱ ----------
     |       |         |             |
     | sqᵍʰ  |  arrSq  |             |
     v       v         v             v
   coeqᵍ==>coeqʰ --> coeqcoeqᵍʰ ···> T
             .               coequalize
             .                       ^
             .                       .
             .........................
                          u

  CoeqsAreIsomorphic : coeqcoeqᶠⁱ ≅ coeqcoeqᵍʰ

-}

  X Y Z W : C M₁   ⇒₁   C M₄
  X = (F B₃ ∘₁ T M₃ ∘₁  F B₂) ∘₁ T M₂ ∘₁ F B₁
  Y = (F B₃ ∘₁ F B₂) ∘₁ T M₂ ∘₁ F B₁
  Z = (F B₃ ∘₁ T M₃ ∘₁ F B₂) ∘₁  F B₁
  W = (F B₃ ∘₁ F B₂) ∘₁ F B₁

  X' Y' Z' W' : C M₁   ⇒₁   C M₄
  X' = F B₃ ∘₁ T M₃ ∘₁ F B₂ ∘₁ T M₂ ∘₁ F B₁
  Y' = F B₃ ∘₁ F B₂ ∘₁ T M₂ ∘₁ F B₁
  Z' = F B₃ ∘₁ T M₃ ∘₁ F B₂ ∘₁  F B₁
  W' = F B₃ ∘₁ F B₂ ∘₁ F B₁

  associatorX : X' ≅ X
  associatorX = associator ⁻¹ ∘ᵢ F B₃ ▷ᵢ (associator ⁻¹)
  
  associatorY : Y' ≅ Y
  associatorY = associator ⁻¹
  
  associatorZ : Z' ≅ Z
  associatorZ = associator ⁻¹ ∘ᵢ F B₃ ▷ᵢ (associator ⁻¹)

  associatorW : W' ≅ W
  associatorW = associator ⁻¹

  f₁ f₂ : X ⇒₂ Y
  f₁ = act-to-the-left B₃ B₂ ◁ (T M₂ ∘₁ F B₁)
  f₂ = act-to-the-right B₃ B₂ ◁ (T M₂ ∘₁ F B₁)

  g₁' g₂' : X' ⇒₂ Z'
  g₁' = F B₃ ▷ T M₃ ▷ act-to-the-left B₂ B₁
  g₂' = F B₃ ▷ T M₃ ▷ act-to-the-right B₂ B₁

  g₁ g₂ : X ⇒₂ Z
  g₁ = _≅_.from associatorZ ∘ᵥ g₁' ∘ᵥ _≅_.to associatorX
  g₂ = _≅_.from associatorZ ∘ᵥ g₂' ∘ᵥ _≅_.to associatorX

  h₁' h₂' : Y' ⇒₂ W'
  h₁' = F B₃ ▷ act-to-the-left B₂ B₁
  h₂' = F B₃ ▷ act-to-the-right B₂ B₁

  h₁ h₂ : Y ⇒₂ W
  h₁ = _≅_.from associatorW ∘ᵥ h₁' ∘ᵥ _≅_.to associatorY
  h₂ = _≅_.from associatorW ∘ᵥ h₂' ∘ᵥ _≅_.to associatorY

  i₁ i₂ : Z ⇒₂ W
  i₁ = act-to-the-left B₃ B₂ ◁ F B₁
  i₂ = act-to-the-right B₃ B₂ ◁ F B₁



  coeqᶠ : Coequalizer f₁ f₂
  coeqᶠ = (CoeqBimods B₃ B₂) coeq-◁ (T M₂ ∘₁ F B₁)

  -- We would like to define
  -- coeqᵍ = postcompCoequalizer (postcompCoequalizer F B₂⊗F B₁ T M₃) F B₃)
  -- but we have to plug in associators at the appropriate positions.
  coeqᵍ : Coequalizer g₁ g₂
  coeqᵍ = CoeqOfIsomorphicDiagram
            (F B₃ ▷-coeq T M₃ ▷-coeq (CoeqBimods B₂ B₁))
            associatorX
            associatorZ
    where
      open Categories.Diagram.Coequalizer.Properties (hom (C M₁) (C M₄)) using (CoeqOfIsomorphicDiagram)
  
  -- We would like to define
  -- coeqʰ = postcompCoequalizer (CoeqBimods B₂ B₁) F B₃
  -- but we have to plug in associators at the appropriate positions.
  coeqʰ : Coequalizer h₁ h₂
  coeqʰ = CoeqOfIsomorphicDiagram
            (F B₃ ▷-coeq (CoeqBimods B₂ B₁))
            associatorY
            associatorW
    where
      open Categories.Diagram.Coequalizer.Properties (hom (C M₁) (C M₄)) using (CoeqOfIsomorphicDiagram)
      
  
  coeqⁱ : Coequalizer i₁ i₂
  coeqⁱ = (CoeqBimods B₃ B₂) coeq-◁ F B₁
  
  f⇒i₁ f⇒i₂ : obj coeqᶠ   ⇒₂   obj coeqⁱ
  f⇒i₁ = act-to-the-left (B₃ ⊗₀ B₂) B₁
  f⇒i₂ = act-to-the-right (B₃ ⊗₀ B₂) B₁
  
  g⇒h₁ g⇒h₂ : obj coeqᵍ ⇒₂ obj coeqʰ
  g⇒h₁ = act-to-the-left B₃ (B₂ ⊗₀ B₁)
  g⇒h₂ = act-to-the-right B₃ (B₂ ⊗₀ B₁)

  abstract
    sq₁ᶠⁱ : CommutativeSquare (arr coeqᶠ) h₁ f⇒i₁ (arr coeqⁱ)
    sq₁ᶠⁱ = begin

      obj (CoeqBimods B₃ B₂) ▷ actionʳ B₁
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ (T M₂ ∘₁ F B₁) ≈⟨ ◁-▷-exchg ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ (F B₃ ∘₁ F B₂) ▷ actionʳ B₁              ≈⟨ refl⟩∘⟨
                                                 switch-fromtoˡ associator α⇒-▷-∘₁ ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ α⇐
        ∘ᵥ F B₃ ▷ F B₂ ▷ actionʳ B₁
        ∘ᵥ α⇒ ∎

      where
        open hom.HomReasoning
        open import Categories.Morphism.Reasoning.Iso (hom (C M₁) (C M₄))

    sq₂ᶠⁱ : CommutativeSquare (arr coeqᶠ) h₂ f⇒i₂ (arr coeqⁱ)
    sq₂ᶠⁱ = begin

      (Bimodule.actionˡ (B₃ ⊗₀ B₂) ◁ F B₁
        ∘ᵥ α⇐)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ (T M₂ ∘₁ F B₁) ≈⟨ assoc₂ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂) ◁ F B₁
        ∘ᵥ α⇐
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ (T M₂ ∘₁ F B₁) ≈⟨ refl⟩∘⟨ α⇐-◁-∘₁ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂) ◁ F B₁
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ T M₂ ◁ F B₁
        ∘ᵥ α⇐                      ≈⟨ sym-assoc₂ ⟩

      (Bimodule.actionˡ (B₃ ⊗₀ B₂) ◁ F B₁
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ T M₂ ◁ F B₁)
        ∘ᵥ α⇐                      ≈⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      (Bimodule.actionˡ (B₃ ⊗₀ B₂)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ T M₂) ◁ F B₁
        ∘ᵥ α⇐                      ≈⟨ ◁-resp-≈ (⟺ actionˡSq-⊗) ⟩∘⟨refl ⟩

      (arr (CoeqBimods B₃ B₂)
        ∘ᵥ F B₃ ▷ actionˡ B₂
        ∘ᵥ α⇒) ◁ F B₁
        ∘ᵥ α⇐                      ≈⟨ ⟺ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      (arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ (F B₃ ▷ actionˡ B₂
        ∘ᵥ α⇒) ◁ F B₁)
        ∘ᵥ α⇐                      ≈⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ (F B₃ ▷ actionˡ B₂
        ∘ᵥ α⇒) ◁ F B₁
        ∘ᵥ α⇐                      ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ ((F B₃ ▷ actionˡ B₂) ◁ F B₁
        ∘ᵥ α⇒ ◁ F B₁)
        ∘ᵥ α⇐                      ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ (F B₃ ▷ actionˡ B₂) ◁ F B₁
        ∘ᵥ α⇒ ◁ F B₁
        ∘ᵥ α⇐                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                 pentagon-conjugate₃ ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ (F B₃ ▷ actionˡ B₂) ◁ F B₁
        ∘ᵥ (α⇐
        ∘ᵥ F B₃ ▷ α⇐)
        ∘ᵥ α⇒                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ (F B₃ ▷ actionˡ B₂) ◁ F B₁
        ∘ᵥ α⇐
        ∘ᵥ F B₃ ▷ α⇐
        ∘ᵥ α⇒                    ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ ((F B₃ ▷ actionˡ B₂) ◁ F B₁
        ∘ᵥ α⇐)
        ∘ᵥ F B₃ ▷ α⇐
        ∘ᵥ α⇒                    ≈⟨ refl⟩∘⟨
                                                 ⟺ α⇐-▷-◁
                                               ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ (α⇐
        ∘ᵥ F B₃ ▷ (actionˡ B₂ ◁ F B₁))
        ∘ᵥ F B₃ ▷ α⇐
        ∘ᵥ α⇒                    ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ α⇐
        ∘ᵥ F B₃ ▷ (actionˡ B₂ ◁ F B₁)
        ∘ᵥ F B₃ ▷ α⇐
        ∘ᵥ α⇒                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                 sym-assoc₂ ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ α⇐
        ∘ᵥ (F B₃ ▷ (actionˡ B₂ ◁ F B₁)
        ∘ᵥ F B₃ ▷ α⇐)
        ∘ᵥ α⇒                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                 ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ α⇐
        ∘ᵥ F B₃ ▷ (actionˡ B₂ ◁ F B₁
                 ∘ᵥ α⇐)
        ∘ᵥ α⇒                    ∎

      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Left-Action B₃ B₂ using (actionˡSq-⊗)

    sq₁ᵍʰ : CommutativeSquare i₁ (arr coeqᵍ) (arr coeqʰ) g⇒h₁
    sq₁ᵍʰ = begin

      (F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇒)
        ∘ᵥ (F B₃ ▷ actionʳ B₂) ◁ F B₁             ≈⟨ assoc₂ ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇒
        ∘ᵥ (F B₃ ▷ actionʳ B₂) ◁ F B₁             ≈⟨ refl⟩∘⟨ α⇒-▷-◁ ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ (actionʳ B₂ ◁ F B₁)
        ∘ᵥ α⇒                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                               ⟺ identity₂ˡ ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ (actionʳ B₂ ◁ F B₁)
        ∘ᵥ id₂
        ∘ᵥ α⇒                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                               ⟺ (_≅_.isoˡ (F B₃ ▷ᵢ associator))
                                             ⟩∘⟨refl ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ (actionʳ B₂ ◁ F B₁)
        ∘ᵥ (F B₃ ▷ α⇐
        ∘ᵥ F B₃ ▷ α⇒)
        ∘ᵥ α⇒                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ (actionʳ B₂ ◁ F B₁)
        ∘ᵥ F B₃ ▷ α⇐
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                  ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ (F B₃ ▷ (actionʳ B₂ ◁ F B₁)
        ∘ᵥ F B₃ ▷ α⇐)
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                  ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ (actionʳ B₂ ◁ F B₁
                 ∘ᵥ α⇐)
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                  ≈⟨ sym-assoc₂ ⟩

      (F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ (actionʳ B₂ ◁ F B₁
                 ∘ᵥ α⇐))
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                  ≈⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      F B₃ ▷ (arr (CoeqBimods B₂ B₁)
            ∘ᵥ actionʳ B₂ ◁ F B₁
            ∘ᵥ α⇐)
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                  ≈⟨ ▷-resp-≈ actionʳSq-⊗ ⟩∘⟨refl ⟩

      F B₃ ▷ (Bimodule.actionʳ (B₂ ⊗₀ B₁)
        ∘ᵥ T M₃ ▷ arr (CoeqBimods B₂ B₁))
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                  ≈⟨ ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      (F B₃ ▷ Bimodule.actionʳ (B₂ ⊗₀ B₁)
        ∘ᵥ F B₃ ▷ T M₃ ▷ arr (CoeqBimods B₂ B₁))
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                  ≈⟨ assoc₂ ⟩

      F B₃ ▷ Bimodule.actionʳ (B₂ ⊗₀ B₁)
        ∘ᵥ F B₃ ▷ T M₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                  ∎

      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Right-Action B₂ B₁ using (actionʳSq-⊗)

    sq₂ᵍʰ : CommutativeSquare i₂ (arr coeqᵍ) (arr coeqʰ) g⇒h₂
    sq₂ᵍʰ = begin

      (F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇒)
        ∘ᵥ (actionˡ B₃ ◁ F B₂
            ∘ᵥ α⇐) ◁ F B₁             ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩

      (F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇒)
        ∘ᵥ actionˡ B₃ ◁ F B₂ ◁ F B₁
        ∘ᵥ α⇐ ◁ F B₁                  ≈⟨ assoc₂ ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇒
        ∘ᵥ actionˡ B₃ ◁ F B₂ ◁ F B₁
        ∘ᵥ α⇐ ◁ F B₁                  ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ (α⇒
        ∘ᵥ actionˡ B₃ ◁ F B₂ ◁ F B₁)
        ∘ᵥ α⇐ ◁ F B₁                  ≈⟨ refl⟩∘⟨ α⇒-◁-∘₁ ⟩∘⟨refl ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ (actionˡ B₃ ◁ (F B₂ ∘₁ F B₁)
        ∘ᵥ α⇒)
        ∘ᵥ α⇐ ◁ F B₁                  ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ actionˡ B₃ ◁ (F B₂ ∘₁ F B₁)
        ∘ᵥ α⇒
        ∘ᵥ α⇐ ◁ F B₁                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                    pentagon-conjugate₄ ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ actionˡ B₃ ◁ (F B₂ ∘₁ F B₁)
        ∘ᵥ α⇐
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                     ≈⟨ sym-assoc₂ ⟩

      (F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ actionˡ B₃ ◁ (F B₂ ∘₁ F B₁))
        ∘ᵥ α⇐
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                     ≈⟨ ◁-▷-exchg ⟩∘⟨refl ⟩

      (actionˡ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ (F B₃ ∘₁ T M₃) ▷ arr (CoeqBimods B₂ B₁))
        ∘ᵥ α⇐
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                     ≈⟨ assoc₂ ⟩

      actionˡ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ (F B₃ ∘₁ T M₃) ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇐
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                     ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      actionˡ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ ((F B₃ ∘₁ T M₃) ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇐)
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                     ≈⟨ refl⟩∘⟨ ⟺ α⇐-▷-∘₁ ⟩∘⟨refl ⟩

      actionˡ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ (α⇐
        ∘ᵥ F B₃ ▷ T M₃ ▷ arr (CoeqBimods B₂ B₁))
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                     ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      actionˡ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ α⇐
        ∘ᵥ F B₃ ▷ T M₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                     ≈⟨ sym-assoc₂ ⟩

      (actionˡ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ α⇐)
        ∘ᵥ F B₃ ▷ T M₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒                     ∎

      where
        open hom.HomReasoning
  -- end abstract --
  
  coeqcoeqᶠⁱ : Coequalizer f⇒i₁ f⇒i₂
  coeqcoeqᶠⁱ = (CoeqBimods (B₃ ⊗₀ B₂) B₁)
  
  coeqcoeqᵍʰ : Coequalizer g⇒h₁ g⇒h₂
  coeqcoeqᵍʰ = (CoeqBimods B₃ (B₂ ⊗₀ B₁))

  
  abstract
    Associator⊗Iso : Bimodule.F ((B₃ ⊗₀ B₂) ⊗₀ B₁) ≅ Bimodule.F (B₃ ⊗₀ B₂ ⊗₀ B₁)
    Associator⊗Iso = CoeqsAreIsomorphic
                     coeqᶠ coeqᵍ coeqʰ coeqⁱ
                     f⇒i₁ f⇒i₂ g⇒h₁ g⇒h₂
                     sq₁ᶠⁱ sq₂ᶠⁱ sq₁ᵍʰ sq₂ᵍʰ
                     coeqcoeqᵍʰ coeqcoeqᶠⁱ
      where
        open Categories.Diagram.Coequalizer.Properties.CoequalizerOfCoequalizer (hom (C M₁) (C M₄)) using (CoeqsAreIsomorphic)

  α⇒⊗ : (Bimodule.F ((B₃ ⊗₀ B₂) ⊗₀ B₁))   ⇒₂   (Bimodule.F (B₃ ⊗₀ B₂ ⊗₀ B₁))
  α⇒⊗ = _≅_.from Associator⊗Iso

  abstract
    hexagon : arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)) ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁) ∘ᵥ α⇒
              ≈ α⇒⊗ ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁
    hexagon = IsoFitsInPentagon
                coeqᶠ coeqᵍ coeqʰ coeqⁱ
                f⇒i₁ f⇒i₂ g⇒h₁ g⇒h₂
                sq₁ᶠⁱ sq₂ᶠⁱ sq₁ᵍʰ sq₂ᵍʰ
                coeqcoeqᵍʰ coeqcoeqᶠⁱ
      where
        open Categories.Diagram.Coequalizer.Properties.CoequalizerOfCoequalizer (hom (C M₁) (C M₄)) using (IsoFitsInPentagon)

open 2-cell using (α⇒⊗; hexagon) public

module Linear-Left where

  abstract
    linearˡ∘arr∘arr : ((Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                      ∘ᵥ α⇒⊗ ◁ T M₁)
                      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
                      ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁
                      ≈ ((α⇒⊗
                      ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
                      ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁
    linearˡ∘arr∘arr = begin

      ((Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ α⇒⊗ ◁ T M₁)
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁ ≈⟨ assoc₂ ⟩∘⟨refl ⟩

      (Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ α⇒⊗ ◁ T M₁
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁ ≈⟨ assoc₂ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ (α⇒⊗ ◁ T M₁
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ α⇒⊗ ◁ T M₁
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                              ∘ᵥ-distr-◁ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ α⇒⊗ ◁ T M₁
        ∘ᵥ (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
            ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁) ◁ T M₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ (α⇒⊗
            ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
            ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁) ◁ T M₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈
                                                   (⟺ hexagon) ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
            ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
            ∘ᵥ α⇒) ◁ T M₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)) ◁ T M₁
        ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)
            ∘ᵥ α⇒) ◁ T M₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)) ◁ T M₁
        ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)) ◁ T M₁
        ∘ᵥ α⇒ ◁ T M₁ ≈⟨ sym-assoc₂ ⟩

      (Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)) ◁ T M₁)
        ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)) ◁ T M₁
        ∘ᵥ α⇒ ◁ T M₁ ≈⟨ ⟺ (actionˡSq-⊗ B₃ (B₂ ⊗₀ B₁)) ⟩∘⟨refl ⟩

      (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ α⇒)
        ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)) ◁ T M₁
        ∘ᵥ α⇒ ◁ T M₁ ≈⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ (F B₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ α⇒)
        ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)) ◁ T M₁
        ∘ᵥ α⇒ ◁ T M₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ α⇒
        ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)) ◁ T M₁
        ∘ᵥ α⇒ ◁ T M₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                   sym-assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ (α⇒
        ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)) ◁ T M₁)
        ∘ᵥ α⇒ ◁ T M₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                   α⇒-▷-◁ ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ (F B₃ ▷ (arr (CoeqBimods B₂ B₁) ◁ T M₁)
        ∘ᵥ α⇒)
        ∘ᵥ α⇒ ◁ T M₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                   assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ F B₃ ▷ (arr (CoeqBimods B₂ B₁) ◁ T M₁)
        ∘ᵥ α⇒
        ∘ᵥ α⇒ ◁ T M₁ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ (F B₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ F B₃ ▷ (arr (CoeqBimods B₂ B₁) ◁ T M₁))
        ∘ᵥ α⇒
        ∘ᵥ α⇒ ◁ T M₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ (Bimodule.actionˡ (B₂ ⊗₀ B₁)
                 ∘ᵥ arr (CoeqBimods B₂ B₁) ◁ T M₁)
        ∘ᵥ α⇒
        ∘ᵥ α⇒ ◁ T M₁                 ≈⟨ refl⟩∘⟨ ▷-resp-≈
                                                   (⟺ (actionˡSq-⊗ B₂ B₁))
                                                 ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ (arr (CoeqBimods B₂ B₁)
                 ∘ᵥ F B₂ ▷ actionˡ B₁
                 ∘ᵥ α⇒)
        ∘ᵥ α⇒
        ∘ᵥ α⇒ ◁ T M₁                 ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ (F B₂ ▷ actionˡ B₁
                 ∘ᵥ α⇒))
        ∘ᵥ α⇒
        ∘ᵥ α⇒ ◁ T M₁                 ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ (F B₂ ▷ actionˡ B₁
                 ∘ᵥ α⇒)
        ∘ᵥ α⇒
        ∘ᵥ α⇒ ◁ T M₁                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ (F B₃ ▷ F B₂ ▷ actionˡ B₁
        ∘ᵥ F B₃ ▷ α⇒)
        ∘ᵥ α⇒
        ∘ᵥ α⇒ ◁ T M₁                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ F B₂ ▷ actionˡ B₁
        ∘ᵥ F B₃ ▷ α⇒
        ∘ᵥ α⇒
        ∘ᵥ α⇒ ◁ T M₁                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   refl⟩∘⟨ pentagon ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ F B₃ ▷ F B₂ ▷ actionˡ B₁
        ∘ᵥ α⇒
        ∘ᵥ α⇒                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   sym-assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ (F B₃ ▷ F B₂ ▷ actionˡ B₁
        ∘ᵥ α⇒)
        ∘ᵥ α⇒                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   ⟺ α⇒-▷-∘₁ ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ (α⇒
        ∘ᵥ (F B₃ ∘₁ F B₂) ▷ actionˡ B₁)
        ∘ᵥ α⇒                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇒
        ∘ᵥ (F B₃ ∘₁ F B₂) ▷ actionˡ B₁
        ∘ᵥ α⇒                      ≈⟨ sym-assoc₂ ⟩

      (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁))
        ∘ᵥ α⇒
        ∘ᵥ (F B₃ ∘₁ F B₂) ▷ actionˡ B₁
        ∘ᵥ α⇒                      ≈⟨ sym-assoc₂ ⟩

      ((arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁))
        ∘ᵥ α⇒)
        ∘ᵥ (F B₃ ∘₁ F B₂) ▷ actionˡ B₁
        ∘ᵥ α⇒                      ≈⟨ assoc₂ ⟩∘⟨refl ⟩

      (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇒)
        ∘ᵥ (F B₃ ∘₁ F B₂) ▷ actionˡ B₁
        ∘ᵥ α⇒                      ≈⟨ hexagon ⟩∘⟨refl ⟩

      (α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
        ∘ᵥ (F B₃ ∘₁ F B₂) ▷ actionˡ B₁
        ∘ᵥ α⇒                      ≈⟨ assoc₂ ⟩

      α⇒⊗
        ∘ᵥ (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
        ∘ᵥ (F B₃ ∘₁ F B₂) ▷ actionˡ B₁
        ∘ᵥ α⇒                      ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ (F B₃ ∘₁ F B₂) ▷ actionˡ B₁
        ∘ᵥ α⇒                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ (arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ (F B₃ ∘₁ F B₂) ▷ actionˡ B₁)
        ∘ᵥ α⇒                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩

      α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ (obj (CoeqBimods B₃ B₂) ▷ actionˡ B₁
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ (F B₁ ∘₁ T M₁))
        ∘ᵥ α⇒                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ obj (CoeqBimods B₃ B₂) ▷ actionˡ B₁
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ (F B₁ ∘₁ T M₁)
        ∘ᵥ α⇒                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   ⟺ α⇒-◁-∘₁ ⟩

      α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ obj (CoeqBimods B₃ B₂) ▷ actionˡ B₁
        ∘ᵥ α⇒
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ (obj (CoeqBimods B₃ B₂) ▷ actionˡ B₁
        ∘ᵥ α⇒)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁      ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      α⇒⊗
        ∘ᵥ (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ obj (CoeqBimods B₃ B₂) ▷ actionˡ B₁
        ∘ᵥ α⇒)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁      ≈⟨ refl⟩∘⟨ actionˡSq-⊗ (B₃ ⊗₀ B₂) B₁
                                                 ⟩∘⟨refl ⟩

      α⇒⊗
        ∘ᵥ (Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁      ≈⟨ sym-assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ (Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁))
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁      ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩

      ((α⇒⊗
        ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁      ∎

      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Left-Action using (actionˡSq-⊗)

  abstract
    linearˡ∘arr : (Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                      ∘ᵥ α⇒⊗ ◁ T M₁)
                      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁
                   ≈ (α⇒⊗
                      ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁
    linearˡ∘arr = Coequalizer⇒Epi
                    ((CoeqBimods B₃ B₂) coeq-◁ F B₁ coeq-◁ T M₁)
                    ((Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                      ∘ᵥ α⇒⊗ ◁ T M₁)
                      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
                    ((α⇒⊗
                      ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
                    linearˡ∘arr∘arr
      where
        open Categories.Diagram.Coequalizer (hom (C M₁) (C M₄)) using (Coequalizer⇒Epi)

  abstract
    linearˡ : Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁) ∘ᵥ α⇒⊗ ◁ T M₁
                      ≈ α⇒⊗ ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
    linearˡ = Coequalizer⇒Epi
                    ((CoeqBimods (B₃ ⊗₀ B₂) B₁) coeq-◁ T M₁)
                    (Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                      ∘ᵥ α⇒⊗ ◁ T M₁)
                    (α⇒⊗
                      ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                    linearˡ∘arr
      where
        open Categories.Diagram.Coequalizer (hom (C M₁) (C M₄)) using (Coequalizer⇒Epi)
  -- end abstract --

module Linear-Right where
  abstract
    linearʳ∘arr∘arr : ((Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                        ∘ᵥ T M₄ ▷ α⇒⊗)
                        ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
                      ≈ ((α⇒⊗
                        ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                        ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
    linearʳ∘arr∘arr = begin

      ((Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ α⇒⊗)
        ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁) ≈⟨ assoc₂ ⟩

      (Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ α⇒⊗)
        ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁) ≈⟨ assoc₂ ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ α⇒⊗
        ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁) ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                ∘ᵥ-distr-▷ ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ α⇒⊗
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                 ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁) ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ (α⇒⊗
                 ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                 ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁) ≈⟨ refl⟩∘⟨ ▷-resp-≈
                                                   (⟺ hexagon) ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
                 ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
                 ∘ᵥ α⇒) ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ T M₄ ▷ (F B₃ ▷ arr (CoeqBimods B₂ B₁)
                 ∘ᵥ α⇒) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ T M₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ T M₄ ▷ α⇒ ≈⟨ sym-assoc₂ ⟩

      (Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)))
        ∘ᵥ T M₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ T M₄ ▷ α⇒ ≈⟨ ⟺ (actionʳSq-⊗ B₃ (B₂ ⊗₀ B₁)) ⟩∘⟨refl ⟩

      (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ actionʳ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ α⇐)
        ∘ᵥ T M₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ T M₄ ▷ α⇒ ≈⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ (actionʳ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ α⇐)
        ∘ᵥ T M₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ T M₄ ▷ α⇒ ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ actionʳ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ α⇐
        ∘ᵥ T M₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ T M₄ ▷ α⇒ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ actionʳ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ (α⇐
        ∘ᵥ T M₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
        ∘ᵥ T M₄ ▷ α⇒ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                   α⇐-▷-∘₁ ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ actionʳ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ ((T M₄ ∘₁ F B₃) ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇐)
        ∘ᵥ T M₄ ▷ α⇒ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ actionʳ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ (T M₄ ∘₁ F B₃) ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇐
        ∘ᵥ T M₄ ▷ α⇒ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ (actionʳ B₃ ◁ obj (CoeqBimods B₂ B₁)
        ∘ᵥ (T M₄ ∘₁ F B₃) ▷ arr (CoeqBimods B₂ B₁))
        ∘ᵥ α⇐
        ∘ᵥ T M₄ ▷ α⇒ ≈⟨ refl⟩∘⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ actionʳ B₃ ◁ (F B₂ ∘₁ F B₁))
        ∘ᵥ α⇐
        ∘ᵥ T M₄ ▷ α⇒ ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ actionʳ B₃ ◁ (F B₂ ∘₁ F B₁)
        ∘ᵥ α⇐
        ∘ᵥ T M₄ ▷ α⇒ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                                   pentagon-conjugate₅ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ actionʳ B₃ ◁ (F B₂ ∘₁ F B₁)
        ∘ᵥ α⇒
        ∘ᵥ α⇐ ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ (actionʳ B₃ ◁ (F B₂ ∘₁ F B₁)
        ∘ᵥ α⇒)
        ∘ᵥ α⇐ ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                            ⟺ α⇒-◁-∘₁ ⟩∘⟨refl ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ (α⇒
        ∘ᵥ actionʳ B₃ ◁ F B₂ ◁ F B₁)
        ∘ᵥ α⇐ ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇒
        ∘ᵥ actionʳ B₃ ◁ F B₂ ◁ F B₁
        ∘ᵥ α⇐ ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇒)
        ∘ᵥ actionʳ B₃ ◁ F B₂ ◁ F B₁
        ∘ᵥ α⇐ ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ sym-assoc₂ ⟩

      (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
        ∘ᵥ α⇒)
        ∘ᵥ actionʳ B₃ ◁ F B₂ ◁ F B₁
        ∘ᵥ α⇐ ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ hexagon ⟩∘⟨refl ⟩

      (α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
        ∘ᵥ actionʳ B₃ ◁ F B₂ ◁ F B₁
        ∘ᵥ α⇐ ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩

      ((α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
        ∘ᵥ actionʳ B₃ ◁ F B₂ ◁ F B₁
        ∘ᵥ α⇐ ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      ((α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
        ∘ᵥ (actionʳ B₃ ◁ F B₂ ◁ F B₁
        ∘ᵥ α⇐ ◁ F B₁)
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      ((α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
        ∘ᵥ (actionʳ B₃ ◁ F B₂
        ∘ᵥ α⇐) ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ (actionʳ B₃ ◁ F B₂
        ∘ᵥ α⇐) ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ (arr (CoeqBimods B₃ B₂) ◁ F B₁
        ∘ᵥ (actionʳ B₃ ◁ F B₂
        ∘ᵥ α⇐) ◁ F B₁)
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      (α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ (arr (CoeqBimods B₃ B₂)
        ∘ᵥ actionʳ B₃ ◁ F B₂
        ∘ᵥ α⇐) ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ ◁-resp-≈
                            (actionʳSq-⊗ B₃ B₂) ⟩∘⟨refl ⟩

      (α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ (Bimodule.actionʳ (B₃ ⊗₀ B₂)
        ∘ᵥ T M₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      (α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ (Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F B₁
        ∘ᵥ (T M₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁)
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F B₁
        ∘ᵥ (T M₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
        ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ α⇐-▷-◁ ⟩

      (α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F B₁
        ∘ᵥ α⇐
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁) ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ (Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F B₁
        ∘ᵥ α⇐)
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁) ≈⟨ assoc₂ ⟩

      α⇒⊗
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ (Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F B₁
        ∘ᵥ α⇐)
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁) ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      α⇒⊗
        ∘ᵥ (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F B₁
        ∘ᵥ α⇐)
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁) ≈⟨ refl⟩∘⟨
                                                actionʳSq-⊗ (B₃ ⊗₀ B₂) B₁
                                              ⟩∘⟨refl ⟩

      α⇒⊗
        ∘ᵥ (Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁) ≈⟨ sym-assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁) ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩

      ((α⇒⊗
        ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
        ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁) ∎

      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Right-Action using (actionʳSq-⊗)

  abstract
    linearʳ∘arr : (Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                    ∘ᵥ T M₄ ▷ α⇒⊗)
                    ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                  ≈ (α⇒⊗
                    ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                    ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    linearʳ∘arr = Coequalizer⇒Epi
                    (T M₄ ▷-coeq ((CoeqBimods B₃ B₂) coeq-◁ F B₁))
                    ((Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                      ∘ᵥ T M₄ ▷ α⇒⊗)
                      ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                    ((α⇒⊗
                      ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                      ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                    linearʳ∘arr∘arr
      where
        open Categories.Diagram.Coequalizer (hom (C M₁) (C M₄)) using (Coequalizer⇒Epi)

  abstract
    linearʳ : Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
              ∘ᵥ T M₄ ▷ α⇒⊗
              ≈ α⇒⊗
              ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
    linearʳ = Coequalizer⇒Epi
                (T M₄ ▷-coeq (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                (Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁) ∘ᵥ T M₄ ▷ α⇒⊗)
                (α⇒⊗ ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                linearʳ∘arr
      where
        open Categories.Diagram.Coequalizer (hom (C M₁) (C M₄)) using (Coequalizer⇒Epi)
-- end abstract --

Associator⊗From : Bimodulehomomorphism ((B₃ ⊗₀ B₂) ⊗₀ B₁) (B₃ ⊗₀ B₂ ⊗₀ B₁)
Associator⊗From = record
  { α = _≅_.from 2-cell.Associator⊗Iso
  ; linearˡ = Linear-Left.linearˡ
  ; linearʳ = Linear-Right.linearʳ
  }

open import Categories.Category.Construction.Bimodules
  renaming (Bimodules to Bimodules₁)
open import Categories.Category.Construction.Bimodules.Properties

Associator⊗ : Categories.Morphism._≅_ (Bimodules₁ M₁ M₄) ((B₃ ⊗₀ B₂) ⊗₀ B₁) (B₃ ⊗₀ B₂ ⊗₀ B₁) 
Associator⊗ = αisIso⇒Iso Associator⊗From α⇒⊗isIso
  where
    open Bimodule-Isomorphism
    α⇒⊗isIso : Categories.Morphism.IsIso (hom (C M₁) (C M₄)) α⇒⊗
    α⇒⊗isIso = record
     { inv = _≅_.to 2-cell.Associator⊗Iso
     ; iso = _≅_.iso 2-cell.Associator⊗Iso
     }
