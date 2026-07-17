{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule


-- We will define the associator in the bicategory of monads and bimodules. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} (localCoeq : LocalCoequalizers 𝒞) {M₁ M₂ M₃ M₄ : Monad 𝒞}
  {B₃ : Bimodule M₃ M₄} {B₂ : Bimodule M₂ M₃} {B₁ : Bimodule M₁ M₂} where

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands

open import Categories.Bicategory.Monad.Bimodule.Homomorphism using (Bimodulehomomorphism)
open ComposeWithLocalCoequalizer 𝒞 localCoeq using (_▷-coeq_; _coeq-◁_)

open Monad using (C; T)
open Bimodule using (F; actionˡ; actionʳ)

import Categories.Diagram.Coequalizer
import Categories.Diagram.Coequalizer.Properties
import Categories.Morphism
import Categories.Morphism.Reasoning
import Categories.Morphism.Reasoning.Iso
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

import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules localCoeq as TensorproductOfBimodules
import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms localCoeq as TensorproductOfHomomorphisms
open TensorproductOfBimodules using (F-⊗; CoeqBimods; act-to-the-left; act-to-the-right) renaming (Tensorproduct to infixr 30 _⊗₀_)
open TensorproductOfBimodules.Left-Action using (actionˡ-⊗; actionˡ-∘)
open TensorproductOfBimodules.Right-Action using (actionʳ-⊗; actionʳ-∘)
open TensorproductOfHomomorphisms using () renaming (Tensorproduct to infixr 30 _⊗₁_)


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
      obj (CoeqBimods B₃ B₂) ▷ actionʳ B₁ ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ (T M₂ ∘₁ F B₁) ≈⟨ ◁-▷-exchg ⟩
      arr (CoeqBimods B₃ B₂) ◁ F B₁ ∘ᵥ (F B₃ ∘₁ F B₂) ▷ actionʳ B₁                   ≈⟨ refl⟩∘⟨ switch-fromtoˡ associator α⇒-▷-∘₁ ⟩
      arr (CoeqBimods B₃ B₂) ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ F B₃ ▷ F B₂ ▷ actionʳ B₁ ∘ᵥ α⇒          ∎
      where
        open hom.HomReasoning
        open Categories.Morphism.Reasoning.Iso (hom (C M₁) (C M₄)) using (switch-fromtoˡ)

    sq₂ᶠⁱ : CommutativeSquare (arr coeqᶠ) h₂ f⇒i₂ (arr coeqⁱ)
    sq₂ᶠⁱ = begin
      (actionˡ-⊗ B₃ B₂ ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ (T M₂ ∘₁ F B₁)                ≈⟨ pullʳ α⇐-◁-∘₁ ⟩
      actionˡ-⊗ B₃ B₂ ◁ F B₁ ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ T M₂ ◁ F B₁ ∘ᵥ α⇐                     ≈⟨ pullˡ ∘ᵥ-distr-◁ ⟩
      (actionˡ-⊗ B₃ B₂ ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ T M₂) ◁ F B₁ ∘ᵥ α⇐                          ≈⟨ ◁-resp-≈ (⟺ actionˡSq-⊗) ⟩∘⟨refl ⟩
      (arr (CoeqBimods B₃ B₂) ∘ᵥ F B₃ ▷ actionˡ B₂ ∘ᵥ α⇒) ◁ F B₁ ∘ᵥ α⇐                         ≈⟨ pushˡ (⟺ ∘ᵥ-distr-◁) ⟩
      arr (CoeqBimods B₃ B₂) ◁ F B₁ ∘ᵥ (F B₃ ▷ actionˡ B₂ ∘ᵥ α⇒) ◁ F B₁ ∘ᵥ α⇐                  ≈⟨ refl⟩∘⟨ pushˡ (⟺ ∘ᵥ-distr-◁) ⟩
      arr (CoeqBimods B₃ B₂) ◁ F B₁ ∘ᵥ (F B₃ ▷ actionˡ B₂) ◁ F B₁ ∘ᵥ α⇒ ◁ F B₁ ∘ᵥ α⇐           ≈⟨ refl⟩∘⟨ pushʳ pentagon-conjugate₃ ⟩
      arr (CoeqBimods B₃ B₂) ◁ F B₁ ∘ᵥ ((F B₃ ▷ actionˡ B₂) ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ F B₃ ▷ α⇐) ∘ᵥ α⇒   ≈⟨ refl⟩∘⟨ pullˡ (⟺ α⇐-▷-◁) ⟩∘⟨refl ⟩
      arr (CoeqBimods B₃ B₂) ◁ F B₁ ∘ᵥ ((α⇐ ∘ᵥ F B₃ ▷ (actionˡ B₂ ◁ F B₁)) ∘ᵥ F B₃ ▷ α⇐) ∘ᵥ α⇒ ≈⟨ refl⟩∘⟨ pullʳ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
      arr (CoeqBimods B₃ B₂) ◁ F B₁ ∘ᵥ (α⇐ ∘ᵥ F B₃ ▷ (actionˡ B₂ ◁ F B₁ ∘ᵥ α⇐)) ∘ᵥ α⇒          ≈⟨ refl⟩∘⟨ assoc₂ ⟩
      arr (CoeqBimods B₃ B₂) ◁ F B₁ ∘ᵥ α⇐ ∘ᵥ F B₃ ▷ (actionˡ B₂ ◁ F B₁ ∘ᵥ α⇐) ∘ᵥ α⇒            ∎
      where
        open hom.HomReasoning
        open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (pullʳ; pullˡ; pushˡ; pushʳ)
        open TensorproductOfBimodules.Left-Action B₃ B₂ using (actionˡSq-⊗)

    sq₁ᵍʰ : CommutativeSquare i₁ (arr coeqᵍ) (arr coeqʰ) g⇒h₁
    sq₁ᵍʰ = begin

      (F B₃ ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ α⇒)
      ∘ᵥ (F B₃ ▷ actionʳ B₂) ◁ F B₁                              ≈⟨ pullʳ α⇒-▷-◁ ⟩
      
      F B₃ ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ F B₃ ▷ (actionʳ B₂ ◁ F B₁)
      ∘ᵥ α⇒                                                      ≈⟨ refl⟩∘⟨ insertInner (_≅_.isoˡ (F B₃ ▷ᵢ associator)) ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ (F B₃ ▷ (actionʳ B₂ ◁ F B₁)
      ∘ᵥ F B₃ ▷ α⇐)
      ∘ᵥ F B₃ ▷ α⇒
      ∘ᵥ α⇒                                                      ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ F B₃ ▷ (actionʳ B₂ ◁ F B₁ ∘ᵥ α⇐)
      ∘ᵥ F B₃ ▷ α⇒
      ∘ᵥ α⇒                                                      ≈⟨ pullˡ ∘ᵥ-distr-▷ ⟩

      F B₃ ▷ (arr (CoeqBimods B₂ B₁) ∘ᵥ actionʳ B₂ ◁ F B₁ ∘ᵥ α⇐)
      ∘ᵥ F B₃ ▷ α⇒
      ∘ᵥ α⇒                                                      ≈⟨ ▷-resp-≈ actionʳSq-⊗ ⟩∘⟨refl ⟩

      F B₃ ▷ (actionʳ-⊗ B₂ B₁ ∘ᵥ T M₃ ▷ arr (CoeqBimods B₂ B₁))
      ∘ᵥ F B₃ ▷ α⇒
      ∘ᵥ α⇒                                                      ≈⟨ pushˡ (⟺ ∘ᵥ-distr-▷) ⟩

      F B₃ ▷ actionʳ-⊗ B₂ B₁
      ∘ᵥ F B₃ ▷ T M₃ ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ F B₃ ▷ α⇒
      ∘ᵥ α⇒                                                      ∎

      where
        open hom.HomReasoning
        open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (pullʳ; pullˡ; pushˡ; insertInner)
        open TensorproductOfBimodules.Right-Action B₂ B₁ using (actionʳSq-⊗)

    sq₂ᵍʰ : CommutativeSquare i₂ (arr coeqᵍ) (arr coeqʰ) g⇒h₂
    sq₂ᵍʰ = begin

      (F B₃ ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ α⇒)
      ∘ᵥ (actionˡ B₃ ◁ F B₂ ∘ᵥ α⇐) ◁ F B₁          ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩

      (F B₃ ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ α⇒)
      ∘ᵥ actionˡ B₃ ◁ F B₂ ◁ F B₁
      ∘ᵥ α⇐ ◁ F B₁                                 ≈⟨ center α⇒-◁-∘₁ ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ (actionˡ B₃ ◁ (F B₂ ∘₁ F B₁)
      ∘ᵥ α⇒)
      ∘ᵥ α⇐ ◁ F B₁                                 ≈⟨ refl⟩∘⟨ pullʳ pentagon-conjugate₄ ⟩

      F B₃ ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ actionˡ B₃ ◁ (F B₂ ∘₁ F B₁)
      ∘ᵥ α⇐
      ∘ᵥ F B₃ ▷ α⇒
      ∘ᵥ α⇒                                        ≈⟨ pullˡ ◁-▷-exchg ⟩

      (actionˡ B₃ ◁ obj (CoeqBimods B₂ B₁)
      ∘ᵥ (F B₃ ∘₁ T M₃) ▷ arr (CoeqBimods B₂ B₁))
      ∘ᵥ α⇐
      ∘ᵥ F B₃ ▷ α⇒
      ∘ᵥ α⇒                                        ≈⟨ center (⟺ α⇐-▷-∘₁) ⟩

      actionˡ B₃ ◁ obj (CoeqBimods B₂ B₁)
      ∘ᵥ (α⇐
      ∘ᵥ F B₃ ▷ T M₃ ▷ arr (CoeqBimods B₂ B₁))
      ∘ᵥ F B₃ ▷ α⇒
      ∘ᵥ α⇒                                        ≈⟨ assoc²δγ ⟩

      (actionˡ B₃ ◁ obj (CoeqBimods B₂ B₁)
      ∘ᵥ α⇐)
      ∘ᵥ F B₃ ▷ T M₃ ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ F B₃ ▷ α⇒
      ∘ᵥ α⇒                                        ∎

      where
        open hom.HomReasoning
        open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (center; pullʳ; pullˡ; assoc²δγ)
  -- end abstract --
  
  coeqcoeqᶠⁱ : Coequalizer f⇒i₁ f⇒i₂
  coeqcoeqᶠⁱ = (CoeqBimods (B₃ ⊗₀ B₂) B₁)
  
  coeqcoeqᵍʰ : Coequalizer g⇒h₁ g⇒h₂
  coeqcoeqᵍʰ = (CoeqBimods B₃ (B₂ ⊗₀ B₁))

  
  abstract
    ---             F ((B₃ ⊗₀ B₂) ⊗₀ B₁)   ≅   F (B₃ ⊗₀ (B₂ ⊗₀ B₁))             ---
    associator-⊗-iso : F-⊗ (B₃ ⊗₀ B₂) B₁   ≅   F-⊗ B₃ (B₂ ⊗₀ B₁)
    associator-⊗-iso = CoeqsAreIsomorphic
                       coeqᶠ coeqᵍ coeqʰ coeqⁱ
                       f⇒i₁ f⇒i₂ g⇒h₁ g⇒h₂
                       sq₁ᶠⁱ sq₂ᶠⁱ sq₁ᵍʰ sq₂ᵍʰ
                       coeqcoeqᵍʰ coeqcoeqᶠⁱ
      where
        open Categories.Diagram.Coequalizer.Properties.CoequalizerOfCoequalizer (hom (C M₁) (C M₄)) using (CoeqsAreIsomorphic)

  α⇒-⊗ : F-⊗ (B₃ ⊗₀ B₂) B₁   ⇒₂   F-⊗ B₃ (B₂ ⊗₀ B₁)
  α⇒-⊗ = _≅_.from associator-⊗-iso

  abstract
    hexagon : arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)) ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁) ∘ᵥ α⇒
            ≈ α⇒-⊗ ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁
    hexagon = IsoFitsInPentagon
                coeqᶠ coeqᵍ coeqʰ coeqⁱ
                f⇒i₁ f⇒i₂ g⇒h₁ g⇒h₂
                sq₁ᶠⁱ sq₂ᶠⁱ sq₁ᵍʰ sq₂ᵍʰ
                coeqcoeqᵍʰ coeqcoeqᶠⁱ
      where
        open Categories.Diagram.Coequalizer.Properties.CoequalizerOfCoequalizer (hom (C M₁) (C M₄)) using (IsoFitsInPentagon)

  abstract
    --- a version of the hexagon in square shape ---
    hexagon-sq : CommutativeSquare
                   α⇒
                   (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
                   (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)) ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁))
                   α⇒-⊗
    hexagon-sq = begin
      (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)) ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)) ∘ᵥ α⇒ ≈⟨ assoc₂ ⟩
      arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)) ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁) ∘ᵥ α⇒   ≈⟨ hexagon ⟩
      α⇒-⊗ ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ∎
      where
        open hom.HomReasoning

open 2-cell using (α⇒-⊗; hexagon; hexagon-sq) public

module Linear-Left where
  private
    {-
    To proof that
       α⇒-⊗ : F ((B₃ ⊗₀ B₂) ⊗₀ B₁) ⇒ F (B₃ ⊗₀ B₂ ⊗₀ B₁)
    is left-linear we first show that
       α⇒ : F B₃ ∘₁ F B₂ ∘₁ F B₁ ⇒₂ (F B₃ ∘₁ F B₂) ∘₁ F B₁
    is left-linear. Here F B₃ ∘₁ F B₂ ∘₁ F B₁ and (F B₃ ∘₁ F B₂) ∘₁ F B₁ are (M₁,M₄)-bimodules with left-action as below.
    -}
    actionˡ-◽∘⦃◽∘◽⦄ : (F B₃  ∘₁ F B₂ ∘₁ F B₁) ∘₁ T M₁   ⇒₂   F B₃ ∘₁ F B₂ ∘₁ F B₁
    actionˡ-◽∘⦃◽∘◽⦄ = F B₃ ▷ actionˡ-∘ B₂ B₁ ∘ᵥ α⇒
    
      where
        open TensorproductOfBimodules.Left-Action using (actionˡ-∘)

    actionˡ-⦃◽∘◽⦄∘◽ : ((F B₃  ∘₁ F B₂) ∘₁ F B₁) ∘₁ T M₁   ⇒₂   (F B₃ ∘₁ F B₂) ∘₁ F B₁
    actionˡ-⦃◽∘◽⦄∘◽ = (F B₃ ∘₁ F B₂) ▷ actionˡ B₁  ∘ᵥ α⇒

    abstract
      linearˡ-α⇒ : actionˡ-◽∘⦃◽∘◽⦄ ∘ᵥ α⇒ ◁ T M₁ ≈ α⇒ ∘ᵥ actionˡ-⦃◽∘◽⦄∘◽
      linearˡ-α⇒ = begin
        actionˡ-◽∘⦃◽∘◽⦄ ∘ᵥ α⇒ ◁ T M₁                            ≈⟨ pushˡ (⟺ ∘ᵥ-distr-▷) ⟩∘⟨refl ⟩
        (F B₃ ▷ F B₂ ▷ actionˡ B₁ ∘ᵥ F B₃ ▷ α⇒ ∘ᵥ α⇒) ∘ᵥ α⇒ ◁ T M₁ ≈⟨ glue (⟺ α⇒-▷-∘₁) pentagon-var ⟩
        α⇒ ∘ᵥ actionˡ-⦃◽∘◽⦄∘◽                                   ∎
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (pushˡ; glue)

      actionˡSq-◽∘⦃◽⊗◽⦄ : F B₃ ▷ arr (CoeqBimods B₂ B₁) ∘ᵥ actionˡ-◽∘⦃◽∘◽⦄
                           ≈ actionˡ-∘ B₃ (B₂ ⊗₀ B₁) ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)) ◁ T M₁
      actionˡSq-◽∘⦃◽⊗◽⦄ = glue′ (▷-resp-sq (actionˡSq-⊗ B₂ B₁)) (⟺ α⇒-▷-◁)
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (glue′)
          open TensorproductOfBimodules.Left-Action using (actionˡSq-⊗)

      actionˡSq-◽⊗⦃◽⊗◽⦄ :
        (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁))
        ∘ᵥ actionˡ-◽∘⦃◽∘◽⦄
        ≈
        actionˡ-⊗ B₃ (B₂ ⊗₀ B₁)
        ∘ᵥ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)) ◁ T M₁
        ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)) ◁ T M₁
      actionˡSq-◽⊗⦃◽⊗◽⦄ = glue (actionˡSq-⊗ B₃ (B₂ ⊗₀ B₁)) actionˡSq-◽∘⦃◽⊗◽⦄
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (glue)
          open TensorproductOfBimodules.Left-Action using (actionˡSq-⊗)

      actionˡSq-⦃◽⊗◽⦄∘◽ : arr (CoeqBimods B₃ B₂) ◁ F B₁ ∘ᵥ actionˡ-⦃◽∘◽⦄∘◽
                           ≈ actionˡ-∘ (B₃ ⊗₀ B₂) B₁ ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁
      actionˡSq-⦃◽⊗◽⦄∘◽ = glue′ (⟺ ◁-▷-exchg) (⟺ α⇒-◁-∘₁)
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (glue′)
          open TensorproductOfBimodules.Left-Action using (actionˡSq-⊗)

      actionˡSq-⦃◽⊗◽⦄⊗◽ :
        (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
        ∘ᵥ actionˡ-⦃◽∘◽⦄∘◽
        ≈
        actionˡ-⊗ (B₃ ⊗₀ B₂) B₁
        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁
      actionˡSq-⦃◽⊗◽⦄⊗◽ = glue (actionˡSq-⊗ (B₃ ⊗₀ B₂) B₁) actionˡSq-⦃◽⊗◽⦄∘◽
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (glue)
          open TensorproductOfBimodules.Left-Action using (actionˡSq-⊗)

  abstract
    linearˡ-∘arr² :
      ((actionˡ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ α⇒-⊗ ◁ T M₁)
      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
      ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁
      ≈
      ((α⇒-⊗
      ∘ᵥ actionˡ-⊗ (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
      ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁

    linearˡ-∘arr² = begin

      ((actionˡ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ α⇒-⊗ ◁ T M₁)
      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
      ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁     ≈⟨ pullʳ ∘ᵥ-distr-◁ ⟩

      (actionˡ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ α⇒-⊗ ◁ T M₁)
      ∘ᵥ (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
         ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁) ◁ T M₁ ≈⟨ pullʳ ∘ᵥ-distr-◁ ⟩

      actionˡ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ (α⇒-⊗
         ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
         ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁) ◁ T M₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ (⟺ hexagon) ⟩

      actionˡ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
         ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
         ∘ᵥ α⇒) ◁ T M₁                            ≈⟨ refl⟩∘⟨ (⟺ ∘ᵥ-distr-◁) ⟩

      actionˡ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)) ◁ T M₁
      ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)
         ∘ᵥ α⇒) ◁ T M₁                            ≈⟨  ⟺ (pull-last ∘ᵥ-distr-◁)  ⟩

      (actionˡ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)) ◁ T M₁
      ∘ᵥ (F B₃ ▷ arr (CoeqBimods B₂ B₁)) ◁ T M₁)
      ∘ᵥ α⇒ ◁ T M₁                                ≈⟨ ⟺ actionˡSq-◽⊗⦃◽⊗◽⦄ ⟩∘⟨refl ⟩

      ((arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁))
      ∘ᵥ actionˡ-◽∘⦃◽∘◽⦄)
      ∘ᵥ α⇒ ◁ T M₁                                ≈⟨ glue hexagon-sq linearˡ-α⇒ ⟩

      α⇒-⊗
      ∘ᵥ (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
      ∘ᵥ actionˡ-⦃◽∘◽⦄∘◽                       ≈⟨ pushʳ actionˡSq-⦃◽⊗◽⦄⊗◽ ⟩

      (α⇒-⊗
      ∘ᵥ actionˡ-⊗ (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁
      ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁     ≈⟨ ⟺ assoc₂ ⟩

      ((α⇒-⊗
      ∘ᵥ actionˡ-⊗ (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
      ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁ ◁ T M₁     ∎

      where
        open hom.HomReasoning
        open Categories.Morphism.Reasoning (hom (C M₁) (C M₄))
          using (pullʳ; pushʳ; pull-last; glue)

  abstract
    linearˡ-∘arr : (actionˡ-⊗ B₃ (B₂ ⊗₀ B₁) ∘ᵥ α⇒-⊗ ◁ T M₁) ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁
                 ≈ (α⇒-⊗ ∘ᵥ actionˡ-⊗ (B₃ ⊗₀ B₂) B₁) ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁
    linearˡ-∘arr = Coequalizer⇒Epi
                    ((CoeqBimods B₃ B₂) coeq-◁ F B₁ coeq-◁ T M₁)
                    ((actionˡ-⊗ B₃ (B₂ ⊗₀ B₁) ∘ᵥ α⇒-⊗ ◁ T M₁) ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
                    ((α⇒-⊗ ∘ᵥ actionˡ-⊗ (B₃ ⊗₀ B₂) B₁) ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁) ◁ T M₁)
                    linearˡ-∘arr²
      where
        open Categories.Diagram.Coequalizer (hom (C M₁) (C M₄)) using (Coequalizer⇒Epi)

  abstract
    linearˡ : actionˡ-⊗ B₃ (B₂ ⊗₀ B₁) ∘ᵥ α⇒-⊗ ◁ T M₁
            ≈ α⇒-⊗ ∘ᵥ actionˡ-⊗ (B₃ ⊗₀ B₂) B₁
    linearˡ = Coequalizer⇒Epi
                ((CoeqBimods (B₃ ⊗₀ B₂) B₁) coeq-◁ T M₁)
                (actionˡ-⊗ B₃ (B₂ ⊗₀ B₁) ∘ᵥ α⇒-⊗ ◁ T M₁)
                (α⇒-⊗ ∘ᵥ actionˡ-⊗ (B₃ ⊗₀ B₂) B₁)
                linearˡ-∘arr
      where
        open Categories.Diagram.Coequalizer (hom (C M₁) (C M₄)) using (Coequalizer⇒Epi)
  -- end abstract --

module Linear-Right where
  private
    {-
    To proof that
       α⇒-⊗ : F ((B₃ ⊗₀ B₂) ⊗₀ B₁) ⇒ F (B₃ ⊗₀ B₂ ⊗₀ B₁)
    is right-linear we first show that
       α⇒ : F B₃ ∘₁ F B₂ ∘₁ F B₁ ⇒₂ (F B₃ ∘₁ F B₂) ∘₁ F B₁
    is right-linear. Here F B₃ ∘₁ F B₂ ∘₁ F B₁ and (F B₃ ∘₁ F B₂) ∘₁ F B₁ are (M₁,M₄)-bimodules with right-action as below.
    -}
    actionʳ-◽∘⦃◽∘◽⦄ : T M₄ ∘₁ F B₃  ∘₁ F B₂ ∘₁ F B₁   ⇒₂   F B₃ ∘₁ F B₂ ∘₁ F B₁
    actionʳ-◽∘⦃◽∘◽⦄ = actionʳ B₃ ◁ (F B₂ ∘₁ F B₁) ∘ᵥ α⇐

    actionʳ-⦃◽∘◽⦄∘◽ : T M₄ ∘₁ (F B₃  ∘₁ F B₂) ∘₁ F B₁   ⇒₂   (F B₃ ∘₁ F B₂) ∘₁ F B₁
    actionʳ-⦃◽∘◽⦄∘◽ = actionʳ-∘ B₃ B₂ ◁ F B₁ ∘ᵥ α⇐
      where
        open TensorproductOfBimodules.Right-Action using (actionʳ-∘)

    abstract
      linearʳ-α⇒ : actionʳ-◽∘⦃◽∘◽⦄ ∘ᵥ T M₄ ▷ α⇒ ≈ α⇒ ∘ᵥ actionʳ-⦃◽∘◽⦄∘◽
      linearʳ-α⇒ = begin
        actionʳ-◽∘⦃◽∘◽⦄ ∘ᵥ T M₄ ▷ α⇒                   ≈⟨ glue (⟺ α⇒-◁-∘₁) pentagon-conjugate₅ ⟩
        α⇒ ∘ᵥ actionʳ B₃ ◁ F B₂ ◁ F B₁ ∘ᵥ α⇐ ◁ F B₁ ∘ᵥ α⇐ ≈⟨ refl⟩∘⟨ pullˡ ∘ᵥ-distr-◁ ⟩
        α⇒ ∘ᵥ actionʳ-⦃◽∘◽⦄∘◽                          ∎
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (glue; pullˡ)

      actionʳSq-◽∘⦃◽⊗◽⦄ : F B₃ ▷ arr (CoeqBimods B₂ B₁) ∘ᵥ actionʳ-◽∘⦃◽∘◽⦄
                           ≈ actionʳ-∘ B₃ (B₂ ⊗₀ B₁) ∘ᵥ T M₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁)
      actionʳSq-◽∘⦃◽⊗◽⦄ = glue′ ◁-▷-exchg (⟺ α⇐-▷-∘₁)
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (glue′; glue)

      actionʳSq-◽⊗⦃◽⊗◽⦄ :
        (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁))
        ∘ᵥ actionʳ-◽∘⦃◽∘◽⦄
        ≈
        (actionʳ-⊗ B₃ (B₂ ⊗₀ B₁)
        ∘ᵥ T M₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
        ∘ᵥ T M₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
      actionʳSq-◽⊗⦃◽⊗◽⦄ = glue (actionʳSq-⊗ B₃ (B₂ ⊗₀ B₁)) actionʳSq-◽∘⦃◽⊗◽⦄
        where
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (glue)
          open TensorproductOfBimodules.Right-Action using (actionʳSq-⊗)

      actionʳSq-⦃◽⊗◽⦄∘◽ : arr (CoeqBimods B₃ B₂) ◁ F B₁ ∘ᵥ actionʳ-⦃◽∘◽⦄∘◽
                           ≈ actionʳ-∘ (B₃ ⊗₀ B₂) B₁ ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
      actionʳSq-⦃◽⊗◽⦄∘◽ = glue′ (◁-resp-sq (actionʳSq-⊗ B₃ B₂)) (⟺ α⇐-▷-◁)
        where
          open hom.HomReasoning
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (glue′)
          open TensorproductOfBimodules.Right-Action using (actionʳSq-⊗)

      actionʳSq-⦃◽⊗◽⦄⊗◽ :
        (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
        ∘ᵥ actionʳ-⦃◽∘◽⦄∘◽
        ≈
        actionʳ-⊗ (B₃ ⊗₀ B₂) B₁
        ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
        ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
      actionʳSq-⦃◽⊗◽⦄⊗◽ = glue (actionʳSq-⊗ (B₃ ⊗₀ B₂) B₁) actionʳSq-⦃◽⊗◽⦄∘◽
        where
          open Categories.Morphism.Reasoning (hom (C M₁) (C M₄)) using (glue)
          open TensorproductOfBimodules.Right-Action using (actionʳSq-⊗)

  abstract
    linearʳ-∘arr² :
      ((actionʳ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ T M₄ ▷ α⇒-⊗)
      ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
      ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
      ≈
      ((α⇒-⊗
      ∘ᵥ actionʳ-⊗ (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
      ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)

    linearʳ-∘arr² = begin

      ((actionʳ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ T M₄ ▷ α⇒-⊗)
      ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
      ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
                                                 ≈⟨ pullʳ ∘ᵥ-distr-▷ ⟩

      (actionʳ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ T M₄ ▷ α⇒-⊗)
      ∘ᵥ T M₄ ▷ (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
         ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
                                                 ≈⟨ pullʳ ∘ᵥ-distr-▷ ⟩

      actionʳ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ T M₄ ▷ (α⇒-⊗
         ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
         ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
                                                 ≈⟨ refl⟩∘⟨ ▷-resp-≈ (⟺ hexagon) ⟩

      actionʳ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
         ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
         ∘ᵥ α⇒)                                  ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩

      actionʳ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ T M₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ T M₄ ▷ (F B₃ ▷ arr (CoeqBimods B₂ B₁)
         ∘ᵥ α⇒)                                  ≈⟨ ⟺ (pull-last ∘ᵥ-distr-▷) ⟩

      (actionʳ-⊗ B₃ (B₂ ⊗₀ B₁)
      ∘ᵥ T M₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ T M₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
      ∘ᵥ T M₄ ▷ α⇒                               ≈⟨ glue′
                                                      (⟺ (actionʳSq-⊗ B₃ (B₂ ⊗₀ B₁)))
                                                      (glue (⟺ ◁-▷-exchg) α⇐-▷-∘₁)
                                                  ⟩∘⟨refl ⟩

      ((arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁))
      ∘ᵥ actionʳ-◽∘⦃◽∘◽⦄)
      ∘ᵥ T M₄ ▷ α⇒                               ≈⟨ extendˡ linearʳ-α⇒ ⟩

      ((arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁))
      ∘ᵥ α⇒)
      ∘ᵥ actionʳ-⦃◽∘◽⦄∘◽                      ≈⟨ assoc₂ ⟩∘⟨refl ⟩

      (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ α⇒)
      ∘ᵥ actionʳ-⦃◽∘◽⦄∘◽                      ≈⟨ pushˡ hexagon ⟩

      α⇒-⊗
      ∘ᵥ (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
      ∘ᵥ actionʳ-⦃◽∘◽⦄∘◽                      ≈⟨ pushʳ actionʳSq-⦃◽⊗◽⦄⊗◽ ⟩

      (α⇒-⊗
      ∘ᵥ actionʳ-⊗ (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)  ≈⟨ ⟺ assoc₂ ⟩

      ((α⇒-⊗
      ∘ᵥ actionʳ-⊗ (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
      ∘ᵥ T M₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)  ∎

      where
        open hom.HomReasoning
        open Categories.Morphism.Reasoning (hom (C M₁) (C M₄))
          using (pullʳ; pushʳ; pull-last; glue′; glue; pull-center; extendˡ; pushˡ)
        open TensorproductOfBimodules.Right-Action using (actionʳSq-⊗)

  abstract
    linearʳ-∘arr : (actionʳ-⊗ B₃ (B₂ ⊗₀ B₁) ∘ᵥ T M₄ ▷ α⇒-⊗) ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                 ≈ (α⇒-⊗ ∘ᵥ actionʳ-⊗ (B₃ ⊗₀ B₂) B₁) ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    linearʳ-∘arr = Coequalizer⇒Epi
                     (T M₄ ▷-coeq ((CoeqBimods B₃ B₂) coeq-◁ F B₁))
                     ((actionʳ-⊗ B₃ (B₂ ⊗₀ B₁) ∘ᵥ T M₄ ▷ α⇒-⊗) ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                     ((α⇒-⊗ ∘ᵥ actionʳ-⊗ (B₃ ⊗₀ B₂) B₁) ∘ᵥ T M₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                     linearʳ-∘arr²
      where
        open Categories.Diagram.Coequalizer (hom (C M₁) (C M₄)) using (Coequalizer⇒Epi)

  abstract
    linearʳ : actionʳ-⊗ B₃ (B₂ ⊗₀ B₁) ∘ᵥ T M₄ ▷ α⇒-⊗
            ≈ α⇒-⊗ ∘ᵥ actionʳ-⊗ (B₃ ⊗₀ B₂) B₁
    linearʳ = Coequalizer⇒Epi
                (T M₄ ▷-coeq (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                (actionʳ-⊗ B₃ (B₂ ⊗₀ B₁) ∘ᵥ T M₄ ▷ α⇒-⊗)
                (α⇒-⊗ ∘ᵥ actionʳ-⊗ (B₃ ⊗₀ B₂) B₁)
                linearʳ-∘arr
      where
        open Categories.Diagram.Coequalizer (hom (C M₁) (C M₄)) using (Coequalizer⇒Epi)
-- end abstract --

associator-⊗-from : Bimodulehomomorphism ((B₃ ⊗₀ B₂) ⊗₀ B₁) (B₃ ⊗₀ B₂ ⊗₀ B₁)
associator-⊗-from = record
  { α = _≅_.from 2-cell.associator-⊗-iso
  ; linearˡ = Linear-Left.linearˡ
  ; linearʳ = Linear-Right.linearʳ
  }

open import Categories.Category.Construction.Bimodules using () renaming (Bimodules to 1-Bimodules)
import Categories.Category.Construction.Bimodules.Properties

associator-⊗ : Categories.Morphism._≅_ (1-Bimodules M₁ M₄) ((B₃ ⊗₀ B₂) ⊗₀ B₁) (B₃ ⊗₀ B₂ ⊗₀ B₁) 
associator-⊗ = αisIso⇒Iso associator-⊗-from α⇒-⊗isIso
  where
    open Categories.Category.Construction.Bimodules.Properties.Bimodule-Isomorphism using (αisIso⇒Iso)
    α⇒-⊗isIso : Categories.Morphism.IsIso (hom (C M₁) (C M₄)) α⇒-⊗
    α⇒-⊗isIso = record
     { inv = _≅_.to 2-cell.associator-⊗-iso
     ; iso = _≅_.iso 2-cell.associator-⊗-iso
     }
