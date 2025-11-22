{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule


-- We will define the associator in the bicategory of monads and bimodules. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ M₄ : Monad 𝒞}
  {B₃ : Bimodule M₃ M₄} {B₂ : Bimodule M₂ M₃} {B₁ : Bimodule M₁ M₂} where

import Categories.Bicategory.LocalCoequalizers
open LocalCoequalizers localCoeq
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct {o} {ℓ} {e} {t} {𝒞} {localCoeq}
private
  _⊗₀_ = TensorproductOfBimodules.B₂⊗B₁
  _⊗₁_ = TensorproductOfHomomorphisms.h₂⊗h₁

infixr 30 _⊗₀_ _⊗₁_

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
import Categories.Diagram.Coequalizer
import Categories.Diagram.Coequalizer.Properties
import Categories.Morphism
import Categories.Category
import Categories.Category.Construction.Core

-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    open Categories.Morphism (hom X Y) public using (_≅_)
    open Categories.Category.Definitions (hom X Y) public using (CommutativeSquare)
    open Categories.Diagram.Coequalizer (hom X Y) public
    open Categories.Diagram.Coequalizer.Properties (hom X Y) public
    open CoequalizerOfCoequalizer using (CoeqsAreIsomorphic) public
    open Categories.Category.Construction.Core.Shorthands (hom X Y) using (_∘ᵢ_; _⁻¹) public

open HomCat


  
open Monad M₁ using () renaming (C to C₁; T to T₁)
open Monad M₂ using () renaming (C to C₂; T to T₂)
open Monad M₃ using () renaming (C to C₃; T to T₃)
open Monad M₄ using () renaming (C to C₄; T to T₄)
open Bimodule B₁ using () renaming (F to F₁; actionʳ to actionʳ₁)
open Bimodule B₂ using () renaming (F to F₂; actionˡ to actionˡ₂; actionʳ to actionʳ₂)
open Bimodule B₃ using () renaming (F to F₃; actionˡ to actionˡ₃; actionʳ to actionʳ₃)
open TensorproductOfBimodules B₂ B₁ using (F₂⊗F₁)
open TensorproductOfBimodules B₃ B₂ using ()
  renaming (F₂⊗F₁ to F₃⊗F₂)
open TensorproductOfBimodules B₃ (B₂ ⊗₀ B₁) using ()
  renaming (F₂⊗F₁ to F₃⊗[F₂⊗F₁])
open TensorproductOfBimodules (B₃ ⊗₀ B₂) B₁ using ()
  renaming (F₂⊗F₁ to [F₃⊗F₂]⊗F₁)


-- The associator is a bimodule. We start by constructing its underlying 2-cell. --

module 2-cell where

  -- We want to use that coequalizers commute with coeuqalizers --
  -- c.f. Categories.Diagram.Coequalizer.Properties.CoequalizerOfCoequalizer --
  -- To apply afformentioned module we need to define the appropriate diagram --
  -- Note that we need to plug in the associators of 𝒞 at the apropriate points to define the diagram --
  {-
        f₁₂
     A ====> B ----> coeqᶠ
     ||      ||       ||
  g₁₂||   h₁₂||  sqᶠⁱ ||
     vv i₁₂  vv       vv        t
     C ====> D ----> coeqⁱ ----------
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

  A B C D : C₁ ⇒₁ C₄
  A = (F₃ ∘₁ T₃ ∘₁  F₂) ∘₁ T₂ ∘₁ F₁
  B = (F₃ ∘₁ F₂) ∘₁ T₂ ∘₁ F₁
  C = (F₃ ∘₁ T₃ ∘₁ F₂) ∘₁  F₁
  D = (F₃ ∘₁ F₂) ∘₁ F₁

  A' B' C' D' : C₁ ⇒₁ C₄
  A' = F₃ ∘₁ T₃ ∘₁ F₂ ∘₁ T₂ ∘₁ F₁
  B' = F₃ ∘₁ F₂ ∘₁ T₂ ∘₁ F₁
  C' = F₃ ∘₁ T₃ ∘₁ F₂ ∘₁  F₁
  D' = F₃ ∘₁ F₂ ∘₁ F₁

  associatorA : A' ≅ A
  associatorA = associator ⁻¹ ∘ᵢ F₃ ▷ᵢ (associator ⁻¹)
  
  associatorB : B' ≅ B
  associatorB = associator ⁻¹
  
  associatorC : C' ≅ C
  associatorC = associator ⁻¹ ∘ᵢ F₃ ▷ᵢ (associator ⁻¹)

  associatorD : D' ≅ D
  associatorD = associator ⁻¹

  f₁ f₂ : A ⇒₂ B
  f₁ = TensorproductOfBimodules.act-to-the-left B₃ B₂ ◁ (T₂ ∘₁ F₁)
  f₂ = TensorproductOfBimodules.act-to-the-right B₃ B₂ ◁ (T₂ ∘₁ F₁)

  g₁' g₂' : A' ⇒₂ C'
  g₁' = F₃ ▷ T₃ ▷ TensorproductOfBimodules.act-to-the-left B₂ B₁
  g₂' = F₃ ▷ T₃ ▷ TensorproductOfBimodules.act-to-the-right B₂ B₁

  g₁ g₂ : A ⇒₂ C
  g₁ = _≅_.from associatorC ∘ᵥ g₁' ∘ᵥ _≅_.to associatorA
  g₂ = _≅_.from associatorC ∘ᵥ g₂' ∘ᵥ _≅_.to associatorA

  h₁' h₂' : B' ⇒₂ D'
  h₁' = F₃ ▷ TensorproductOfBimodules.act-to-the-left B₂ B₁
  h₂' = F₃ ▷ TensorproductOfBimodules.act-to-the-right B₂ B₁

  h₁ h₂ : B ⇒₂ D
  h₁ = _≅_.from associatorD ∘ᵥ h₁' ∘ᵥ _≅_.to associatorB
  h₂ = _≅_.from associatorD ∘ᵥ h₂' ∘ᵥ _≅_.to associatorB

  i₁ i₂ : C ⇒₂ D
  i₁ = TensorproductOfBimodules.act-to-the-left B₃ B₂ ◁ F₁
  i₂ = TensorproductOfBimodules.act-to-the-right B₃ B₂ ◁ F₁



  coeqᶠ : Coequalizer f₁ f₂
  coeqᶠ = precompCoequalizer F₃⊗F₂ (T₂ ∘₁ F₁)

  -- We would like to define
  -- coeqᵍ = postcompCoequalizer (postcompCoequalizer F₂⊗F₁ T₃) F₃)
  -- but we have to plug in associators at the appropriate positions.
  coeqᵍ : Coequalizer g₁ g₂
  coeqᵍ = CoeqOfIsomorphicDiagram
            (postcompCoequalizer (postcompCoequalizer F₂⊗F₁ T₃) F₃)
            associatorA
            associatorC
  
  -- We would like to define
  -- coeqʰ = postcompCoequalizer F₂⊗F₁ F₃
  -- but we have to plug in associators at the appropriate positions.
  coeqʰ : Coequalizer h₁ h₂
  coeqʰ = CoeqOfIsomorphicDiagram
            (postcompCoequalizer F₂⊗F₁ F₃)
            associatorB
            associatorD
      
  
  coeqⁱ : Coequalizer i₁ i₂
  coeqⁱ = precompCoequalizer F₃⊗F₂ F₁
  
  f⇒i₁ f⇒i₂ : Coequalizer.obj coeqᶠ ⇒₂ Coequalizer.obj coeqⁱ
  f⇒i₁ = TensorproductOfBimodules.act-to-the-left (B₃ ⊗₀ B₂) B₁
  f⇒i₂ = TensorproductOfBimodules.act-to-the-right (B₃ ⊗₀ B₂) B₁
  
  g⇒h₁ g⇒h₂ : Coequalizer.obj coeqᵍ ⇒₂ Coequalizer.obj coeqʰ
  g⇒h₁ = TensorproductOfBimodules.act-to-the-left B₃ (B₂ ⊗₀ B₁)
  g⇒h₂ = TensorproductOfBimodules.act-to-the-right B₃ (B₂ ⊗₀ B₁)

  abstract
    sq₁ᶠⁱ : CommutativeSquare (Coequalizer.arr coeqᶠ) h₁ f⇒i₁ (Coequalizer.arr coeqⁱ)
    sq₁ᶠⁱ = begin

      Coequalizer.obj F₃⊗F₂ ▷ actionʳ₁
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ (T₂ ∘₁ F₁) ≈⟨ ◁-▷-exchg ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ (F₃ ∘₁ F₂) ▷ actionʳ₁              ≈⟨ refl⟩∘⟨
                                                 switch-fromtoˡ associator α⇒-▷-∘₁ ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ associator.to
        ∘ᵥ F₃ ▷ F₂ ▷ actionʳ₁
        ∘ᵥ associator.from ∎

      where
        open hom.HomReasoning
        open import Categories.Morphism.Reasoning.Iso (hom C₁ C₄)

    sq₂ᶠⁱ : CommutativeSquare (Coequalizer.arr coeqᶠ) h₂ f⇒i₂ (Coequalizer.arr coeqⁱ)
    sq₂ᶠⁱ = begin

      (Bimodule.actionˡ (B₃ ⊗₀ B₂) ◁ F₁
        ∘ᵥ associator.to)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ (T₂ ∘₁ F₁) ≈⟨ assoc₂ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂) ◁ F₁
        ∘ᵥ associator.to
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ (T₂ ∘₁ F₁) ≈⟨ refl⟩∘⟨ α⇐-◁-∘₁ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂) ◁ F₁
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ T₂ ◁ F₁
        ∘ᵥ associator.to                      ≈⟨ sym-assoc₂ ⟩

      (Bimodule.actionˡ (B₃ ⊗₀ B₂) ◁ F₁
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ T₂ ◁ F₁)
        ∘ᵥ associator.to                      ≈⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      (Bimodule.actionˡ (B₃ ⊗₀ B₂)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ T₂) ◁ F₁
        ∘ᵥ associator.to                      ≈⟨ ◁-resp-≈ (⟺ actionˡSq) ⟩∘⟨refl ⟩

      (Coequalizer.arr F₃⊗F₂
        ∘ᵥ F₃ ▷ actionˡ₂
        ∘ᵥ associator.from) ◁ F₁
        ∘ᵥ associator.to                      ≈⟨ ⟺ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      (Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ (F₃ ▷ actionˡ₂
        ∘ᵥ associator.from) ◁ F₁)
        ∘ᵥ associator.to                      ≈⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ (F₃ ▷ actionˡ₂
        ∘ᵥ associator.from) ◁ F₁
        ∘ᵥ associator.to                      ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ ((F₃ ▷ actionˡ₂) ◁ F₁
        ∘ᵥ associator.from ◁ F₁)
        ∘ᵥ associator.to                      ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ (F₃ ▷ actionˡ₂) ◁ F₁
        ∘ᵥ associator.from ◁ F₁
        ∘ᵥ associator.to                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                 pentagon-conjugate₃ ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ (F₃ ▷ actionˡ₂) ◁ F₁
        ∘ᵥ (associator.to
        ∘ᵥ F₃ ▷ associator.to)
        ∘ᵥ associator.from                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ (F₃ ▷ actionˡ₂) ◁ F₁
        ∘ᵥ associator.to
        ∘ᵥ F₃ ▷ associator.to
        ∘ᵥ associator.from                    ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ ((F₃ ▷ actionˡ₂) ◁ F₁
        ∘ᵥ associator.to)
        ∘ᵥ F₃ ▷ associator.to
        ∘ᵥ associator.from                    ≈⟨ refl⟩∘⟨
                                                 ⟺ α⇐-▷-◁
                                               ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ (associator.to
        ∘ᵥ F₃ ▷ (actionˡ₂ ◁ F₁))
        ∘ᵥ F₃ ▷ associator.to
        ∘ᵥ associator.from                    ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ associator.to
        ∘ᵥ F₃ ▷ (actionˡ₂ ◁ F₁)
        ∘ᵥ F₃ ▷ associator.to
        ∘ᵥ associator.from                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                 sym-assoc₂ ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ associator.to
        ∘ᵥ (F₃ ▷ (actionˡ₂ ◁ F₁)
        ∘ᵥ F₃ ▷ associator.to)
        ∘ᵥ associator.from                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                 ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ associator.to
        ∘ᵥ F₃ ▷ (actionˡ₂ ◁ F₁
                 ∘ᵥ associator.to)
        ∘ᵥ associator.from                    ∎

      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Left-Action B₃ B₂ using (actionˡSq)

    sq₁ᵍʰ : CommutativeSquare i₁ (Coequalizer.arr coeqᵍ) (Coequalizer.arr coeqʰ) g⇒h₁
    sq₁ᵍʰ = begin

      (F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.from)
        ∘ᵥ (F₃ ▷ actionʳ₂) ◁ F₁             ≈⟨ assoc₂ ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.from
        ∘ᵥ (F₃ ▷ actionʳ₂) ◁ F₁             ≈⟨ refl⟩∘⟨ α⇒-▷-◁ ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ (actionʳ₂ ◁ F₁)
        ∘ᵥ associator.from                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                               ⟺ identity₂ˡ ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ (actionʳ₂ ◁ F₁)
        ∘ᵥ id₂
        ∘ᵥ associator.from                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                               ⟺ (_≅_.isoˡ (F₃ ▷ᵢ associator))
                                             ⟩∘⟨refl ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ (actionʳ₂ ◁ F₁)
        ∘ᵥ (F₃ ▷ associator.to
        ∘ᵥ F₃ ▷ associator.from)
        ∘ᵥ associator.from                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ (actionʳ₂ ◁ F₁)
        ∘ᵥ F₃ ▷ associator.to
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                  ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ (F₃ ▷ (actionʳ₂ ◁ F₁)
        ∘ᵥ F₃ ▷ associator.to)
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                  ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ (actionʳ₂ ◁ F₁
                 ∘ᵥ associator.to)
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                  ≈⟨ sym-assoc₂ ⟩

      (F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ (actionʳ₂ ◁ F₁
                 ∘ᵥ associator.to))
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                  ≈⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      F₃ ▷ (Coequalizer.arr F₂⊗F₁
            ∘ᵥ actionʳ₂ ◁ F₁
            ∘ᵥ associator.to)
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                  ≈⟨ ▷-resp-≈ actionʳSq ⟩∘⟨refl ⟩

      F₃ ▷ (Bimodule.actionʳ (B₂ ⊗₀ B₁)
        ∘ᵥ T₃ ▷ Coequalizer.arr F₂⊗F₁)
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                  ≈⟨ ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      (F₃ ▷ Bimodule.actionʳ (B₂ ⊗₀ B₁)
        ∘ᵥ F₃ ▷ T₃ ▷ Coequalizer.arr F₂⊗F₁)
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                  ≈⟨ assoc₂ ⟩

      F₃ ▷ Bimodule.actionʳ (B₂ ⊗₀ B₁)
        ∘ᵥ F₃ ▷ T₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                  ∎

      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Right-Action B₂ B₁ using (actionʳSq)

    sq₂ᵍʰ : CommutativeSquare i₂ (Coequalizer.arr coeqᵍ) (Coequalizer.arr coeqʰ) g⇒h₂
    sq₂ᵍʰ = begin

      (F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.from)
        ∘ᵥ (actionˡ₃ ◁ F₂
            ∘ᵥ associator.to) ◁ F₁             ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩

      (F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.from)
        ∘ᵥ actionˡ₃ ◁ F₂ ◁ F₁
        ∘ᵥ associator.to ◁ F₁                  ≈⟨ assoc₂ ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.from
        ∘ᵥ actionˡ₃ ◁ F₂ ◁ F₁
        ∘ᵥ associator.to ◁ F₁                  ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ (associator.from
        ∘ᵥ actionˡ₃ ◁ F₂ ◁ F₁)
        ∘ᵥ associator.to ◁ F₁                  ≈⟨ refl⟩∘⟨ α⇒-◁-∘₁ ⟩∘⟨refl ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ (actionˡ₃ ◁ (F₂ ∘₁ F₁)
        ∘ᵥ associator.from)
        ∘ᵥ associator.to ◁ F₁                  ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ actionˡ₃ ◁ (F₂ ∘₁ F₁)
        ∘ᵥ associator.from
        ∘ᵥ associator.to ◁ F₁                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                    pentagon-conjugate₄ ⟩

      F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ actionˡ₃ ◁ (F₂ ∘₁ F₁)
        ∘ᵥ associator.to
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                     ≈⟨ sym-assoc₂ ⟩

      (F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ actionˡ₃ ◁ (F₂ ∘₁ F₁))
        ∘ᵥ associator.to
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                     ≈⟨ ◁-▷-exchg ⟩∘⟨refl ⟩

      (actionˡ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ (F₃ ∘₁ T₃) ▷ Coequalizer.arr F₂⊗F₁)
        ∘ᵥ associator.to
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                     ≈⟨ assoc₂ ⟩

      actionˡ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ (F₃ ∘₁ T₃) ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.to
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                     ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      actionˡ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ ((F₃ ∘₁ T₃) ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.to)
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                     ≈⟨ refl⟩∘⟨ ⟺ α⇐-▷-∘₁ ⟩∘⟨refl ⟩

      actionˡ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ (associator.to
        ∘ᵥ F₃ ▷ T₃ ▷ Coequalizer.arr F₂⊗F₁)
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                     ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      actionˡ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ associator.to
        ∘ᵥ F₃ ▷ T₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                     ≈⟨ sym-assoc₂ ⟩

      (actionˡ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ associator.to)
        ∘ᵥ F₃ ▷ T₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from                     ∎

      where
        open hom.HomReasoning
  -- end abstract --
  
  coeqcoeqᶠⁱ : Coequalizer f⇒i₁ f⇒i₂
  coeqcoeqᶠⁱ = [F₃⊗F₂]⊗F₁
  
  coeqcoeqᵍʰ : Coequalizer g⇒h₁ g⇒h₂
  coeqcoeqᵍʰ = F₃⊗[F₂⊗F₁]

  

  Associator⊗Iso : Bimodule.F ((B₃ ⊗₀ B₂) ⊗₀ B₁) ≅ Bimodule.F (B₃ ⊗₀ B₂ ⊗₀ B₁)
  Associator⊗Iso = CoeqsAreIsomorphic
                    coeqᶠ coeqᵍ coeqʰ coeqⁱ
                    f⇒i₁ f⇒i₂ g⇒h₁ g⇒h₂
                    sq₁ᶠⁱ sq₂ᶠⁱ sq₁ᵍʰ sq₂ᵍʰ
                    coeqcoeqᵍʰ coeqcoeqᶠⁱ
                    
  α⇒⊗ : (Bimodule.F ((B₃ ⊗₀ B₂) ⊗₀ B₁)) ⇒₂ (Bimodule.F (B₃ ⊗₀ B₂ ⊗₀ B₁))
  α⇒⊗ = _≅_.from Associator⊗Iso

  hexagon : Coequalizer.arr F₃⊗[F₂⊗F₁] ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁ ∘ᵥ associator.from
             ≈ α⇒⊗ ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁
  hexagon = IsoFitsInPentagon
                coeqᶠ coeqᵍ coeqʰ coeqⁱ
                f⇒i₁ f⇒i₂ g⇒h₁ g⇒h₂
                sq₁ᶠⁱ sq₂ᶠⁱ sq₁ᵍʰ sq₂ᵍʰ
                coeqcoeqᵍʰ coeqcoeqᶠⁱ
    where
      open CoequalizerOfCoequalizer using (IsoFitsInPentagon)

open 2-cell using (α⇒⊗; hexagon) public

module Linear-Left where
  open Bimodule B₁ using () renaming (actionˡ to actionˡ₁)

  abstract
    linearˡ∘arr∘arr : ((Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                      ∘ᵥ α⇒⊗ ◁ T₁)
                      ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁)
                      ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁
                      ≈ ((α⇒⊗
                      ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                      ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁)
                      ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁
    linearˡ∘arr∘arr = begin

      ((Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ α⇒⊗ ◁ T₁)
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁ ≈⟨ assoc₂ ⟩∘⟨refl ⟩

      (Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ α⇒⊗ ◁ T₁
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁ ≈⟨ assoc₂ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ (α⇒⊗ ◁ T₁
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ α⇒⊗ ◁ T₁
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                              ∘ᵥ-distr-◁ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ α⇒⊗ ◁ T₁
        ∘ᵥ (Coequalizer.arr [F₃⊗F₂]⊗F₁
            ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁) ◁ T₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ (α⇒⊗
            ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
            ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈
                                                   (⟺ hexagon) ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ (Coequalizer.arr F₃⊗[F₂⊗F₁]
            ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
            ∘ᵥ associator.from) ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ Coequalizer.arr F₃⊗[F₂⊗F₁] ◁ T₁
        ∘ᵥ (F₃ ▷ Coequalizer.arr F₂⊗F₁
            ∘ᵥ associator.from) ◁ T₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩

      Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ Coequalizer.arr F₃⊗[F₂⊗F₁] ◁ T₁
        ∘ᵥ (F₃ ▷ Coequalizer.arr F₂⊗F₁) ◁ T₁
        ∘ᵥ associator.from ◁ T₁ ≈⟨ sym-assoc₂ ⟩

      (Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ Coequalizer.arr F₃⊗[F₂⊗F₁] ◁ T₁)
        ∘ᵥ (F₃ ▷ Coequalizer.arr F₂⊗F₁) ◁ T₁
        ∘ᵥ associator.from ◁ T₁ ≈⟨ ⟺ actionˡSqB₃⊗[B₂⊗B₁] ⟩∘⟨refl ⟩

      (Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ associator.from)
        ∘ᵥ (F₃ ▷ Coequalizer.arr F₂⊗F₁) ◁ T₁
        ∘ᵥ associator.from ◁ T₁ ≈⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ (F₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ associator.from)
        ∘ᵥ (F₃ ▷ Coequalizer.arr F₂⊗F₁) ◁ T₁
        ∘ᵥ associator.from ◁ T₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ associator.from
        ∘ᵥ (F₃ ▷ Coequalizer.arr F₂⊗F₁) ◁ T₁
        ∘ᵥ associator.from ◁ T₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                   sym-assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ (associator.from
        ∘ᵥ (F₃ ▷ Coequalizer.arr F₂⊗F₁) ◁ T₁)
        ∘ᵥ associator.from ◁ T₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                   α⇒-▷-◁ ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ (F₃ ▷ (Coequalizer.arr F₂⊗F₁ ◁ T₁)
        ∘ᵥ associator.from)
        ∘ᵥ associator.from ◁ T₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                   assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ F₃ ▷ (Coequalizer.arr F₂⊗F₁ ◁ T₁)
        ∘ᵥ associator.from
        ∘ᵥ associator.from ◁ T₁ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ (F₃ ▷ Bimodule.actionˡ (B₂ ⊗₀ B₁)
        ∘ᵥ F₃ ▷ (Coequalizer.arr F₂⊗F₁ ◁ T₁))
        ∘ᵥ associator.from
        ∘ᵥ associator.from ◁ T₁ ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ (Bimodule.actionˡ (B₂ ⊗₀ B₁)
                 ∘ᵥ Coequalizer.arr F₂⊗F₁ ◁ T₁)
        ∘ᵥ associator.from
        ∘ᵥ associator.from ◁ T₁                 ≈⟨ refl⟩∘⟨ ▷-resp-≈
                                                   (⟺ actionˡSqB₂⊗B₁)
                                                 ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ (Coequalizer.arr F₂⊗F₁
                 ∘ᵥ F₂ ▷ actionˡ₁
                 ∘ᵥ associator.from)
        ∘ᵥ associator.from
        ∘ᵥ associator.from ◁ T₁                 ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ (F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ (F₂ ▷ actionˡ₁
                 ∘ᵥ associator.from))
        ∘ᵥ associator.from
        ∘ᵥ associator.from ◁ T₁                 ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ (F₂ ▷ actionˡ₁
                 ∘ᵥ associator.from)
        ∘ᵥ associator.from
        ∘ᵥ associator.from ◁ T₁                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ (F₃ ▷ F₂ ▷ actionˡ₁
        ∘ᵥ F₃ ▷ associator.from)
        ∘ᵥ associator.from
        ∘ᵥ associator.from ◁ T₁                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ F₂ ▷ actionˡ₁
        ∘ᵥ F₃ ▷ associator.from
        ∘ᵥ associator.from
        ∘ᵥ associator.from ◁ T₁                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   refl⟩∘⟨ pentagon ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ F₃ ▷ F₂ ▷ actionˡ₁
        ∘ᵥ associator.from
        ∘ᵥ associator.from                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   sym-assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ (F₃ ▷ F₂ ▷ actionˡ₁
        ∘ᵥ associator.from)
        ∘ᵥ associator.from                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   ⟺ α⇒-▷-∘₁ ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ (associator.from
        ∘ᵥ (F₃ ∘₁ F₂) ▷ actionˡ₁)
        ∘ᵥ associator.from                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.from
        ∘ᵥ (F₃ ∘₁ F₂) ▷ actionˡ₁
        ∘ᵥ associator.from                      ≈⟨ sym-assoc₂ ⟩

      (Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁)
        ∘ᵥ associator.from
        ∘ᵥ (F₃ ∘₁ F₂) ▷ actionˡ₁
        ∘ᵥ associator.from                      ≈⟨ sym-assoc₂ ⟩

      ((Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁)
        ∘ᵥ associator.from)
        ∘ᵥ (F₃ ∘₁ F₂) ▷ actionˡ₁
        ∘ᵥ associator.from                      ≈⟨ assoc₂ ⟩∘⟨refl ⟩

      (Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.from)
        ∘ᵥ (F₃ ∘₁ F₂) ▷ actionˡ₁
        ∘ᵥ associator.from                      ≈⟨ hexagon ⟩∘⟨refl ⟩

      (α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁)
        ∘ᵥ (F₃ ∘₁ F₂) ▷ actionˡ₁
        ∘ᵥ associator.from                      ≈⟨ assoc₂ ⟩

      α⇒⊗
        ∘ᵥ (Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁)
        ∘ᵥ (F₃ ∘₁ F₂) ▷ actionˡ₁
        ∘ᵥ associator.from                      ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ (F₃ ∘₁ F₂) ▷ actionˡ₁
        ∘ᵥ associator.from                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ (Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ (F₃ ∘₁ F₂) ▷ actionˡ₁)
        ∘ᵥ associator.from                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩

      α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ (Coequalizer.obj F₃⊗F₂ ▷ actionˡ₁
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ (F₁ ∘₁ T₁))
        ∘ᵥ associator.from                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ Coequalizer.obj F₃⊗F₂ ▷ actionˡ₁
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ (F₁ ∘₁ T₁)
        ∘ᵥ associator.from                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                                                   ⟺ α⇒-◁-∘₁ ⟩

      α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ Coequalizer.obj F₃⊗F₂ ▷ actionˡ₁
        ∘ᵥ associator.from
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ (Coequalizer.obj F₃⊗F₂ ▷ actionˡ₁
        ∘ᵥ associator.from)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁      ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      α⇒⊗
        ∘ᵥ (Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ Coequalizer.obj F₃⊗F₂ ▷ actionˡ₁
        ∘ᵥ associator.from)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁      ≈⟨ refl⟩∘⟨ actionˡSq[B₃⊗B₂]⊗B₁
                                                 ⟩∘⟨refl ⟩

      α⇒⊗
        ∘ᵥ (Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁      ≈⟨ sym-assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ (Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁))
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁      ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩

      ((α⇒⊗
        ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ◁ T₁      ∎

      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Left-Action B₃ (B₂ ⊗₀ B₁)
          using () renaming (actionˡSq to actionˡSqB₃⊗[B₂⊗B₁])
        open TensorproductOfBimodules.Left-Action B₂ B₁
          using () renaming (actionˡSq to actionˡSqB₂⊗B₁)
        open TensorproductOfBimodules.Left-Action (B₃ ⊗₀ B₂) B₁
          using () renaming (actionˡSq to actionˡSq[B₃⊗B₂]⊗B₁)

    linearˡ∘arr : (Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                      ∘ᵥ α⇒⊗ ◁ T₁)
                      ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁
                   ≈ (α⇒⊗
                      ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                      ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁
    linearˡ∘arr = Coequalizer⇒Epi
                    (precompCoequalizer (precompCoequalizer F₃⊗F₂ F₁) T₁)
                    ((Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                      ∘ᵥ α⇒⊗ ◁ T₁)
                      ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁)
                    ((α⇒⊗
                      ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                      ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁ ◁ T₁)
                    linearˡ∘arr∘arr

    linearˡ : Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁) ∘ᵥ α⇒⊗ ◁ T₁
                      ≈ α⇒⊗ ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
    linearˡ = Coequalizer⇒Epi
                    (precompCoequalizer [F₃⊗F₂]⊗F₁ T₁)
                    (Bimodule.actionˡ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                      ∘ᵥ α⇒⊗ ◁ T₁)
                    (α⇒⊗
                      ∘ᵥ Bimodule.actionˡ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                    linearˡ∘arr
  -- end abstract --

module Linear-Right where
  abstract
    linearʳ∘arr∘arr : ((Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                        ∘ᵥ T₄ ▷ α⇒⊗)
                        ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁)
                        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁)
                      ≈ ((α⇒⊗
                        ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                        ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁)
                        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁)
    linearʳ∘arr∘arr = begin

      ((Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T₄ ▷ α⇒⊗)
        ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁) ≈⟨ assoc₂ ⟩

      (Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T₄ ▷ α⇒⊗)
        ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁) ≈⟨ assoc₂ ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T₄ ▷ α⇒⊗
        ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁) ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                                ∘ᵥ-distr-▷ ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T₄ ▷ α⇒⊗
        ∘ᵥ T₄ ▷ (Coequalizer.arr [F₃⊗F₂]⊗F₁
                 ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁) ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T₄ ▷ (α⇒⊗
                 ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
                 ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁) ≈⟨ refl⟩∘⟨ ▷-resp-≈
                                                   (⟺ hexagon) ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗[F₂⊗F₁]
                 ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
                 ∘ᵥ associator.from) ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T₄ ▷ Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ T₄ ▷ (F₃ ▷ Coequalizer.arr F₂⊗F₁
                 ∘ᵥ associator.from) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩

      Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T₄ ▷ Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ T₄ ▷ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ T₄ ▷ associator.from ≈⟨ sym-assoc₂ ⟩

      (Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
        ∘ᵥ T₄ ▷ Coequalizer.arr F₃⊗[F₂⊗F₁])
        ∘ᵥ T₄ ▷ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ T₄ ▷ associator.from ≈⟨ ⟺ actionʳSqF₃⊗[F₂⊗F₁] ⟩∘⟨refl ⟩

      (Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ actionʳ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ associator.to)
        ∘ᵥ T₄ ▷ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ T₄ ▷ associator.from ≈⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ (actionʳ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ associator.to)
        ∘ᵥ T₄ ▷ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ T₄ ▷ associator.from ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ actionʳ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ associator.to
        ∘ᵥ T₄ ▷ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ T₄ ▷ associator.from ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ actionʳ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ (associator.to
        ∘ᵥ T₄ ▷ F₃ ▷ Coequalizer.arr F₂⊗F₁)
        ∘ᵥ T₄ ▷ associator.from ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                   α⇐-▷-∘₁ ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ actionʳ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ ((T₄ ∘₁ F₃) ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.to)
        ∘ᵥ T₄ ▷ associator.from ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ actionʳ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ (T₄ ∘₁ F₃) ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.to
        ∘ᵥ T₄ ▷ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ (actionʳ₃ ◁ Coequalizer.obj F₂⊗F₁
        ∘ᵥ (T₄ ∘₁ F₃) ▷ Coequalizer.arr F₂⊗F₁)
        ∘ᵥ associator.to
        ∘ᵥ T₄ ▷ associator.from ≈⟨ refl⟩∘⟨ ⟺ ◁-▷-exchg ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ (F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ actionʳ₃ ◁ (F₂ ∘₁ F₁))
        ∘ᵥ associator.to
        ∘ᵥ T₄ ▷ associator.from ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ actionʳ₃ ◁ (F₂ ∘₁ F₁)
        ∘ᵥ associator.to
        ∘ᵥ T₄ ▷ associator.from ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                                   pentagon-conjugate₅ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ actionʳ₃ ◁ (F₂ ∘₁ F₁)
        ∘ᵥ associator.from
        ∘ᵥ associator.to ◁ F₁
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ (actionʳ₃ ◁ (F₂ ∘₁ F₁)
        ∘ᵥ associator.from)
        ∘ᵥ associator.to ◁ F₁
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                            ⟺ α⇒-◁-∘₁ ⟩∘⟨refl ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ (associator.from
        ∘ᵥ actionʳ₃ ◁ F₂ ◁ F₁)
        ∘ᵥ associator.to ◁ F₁
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.from
        ∘ᵥ actionʳ₃ ◁ F₂ ◁ F₁
        ∘ᵥ associator.to ◁ F₁
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ (F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.from)
        ∘ᵥ actionʳ₃ ◁ F₂ ◁ F₁
        ∘ᵥ associator.to ◁ F₁
        ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩

      (Coequalizer.arr F₃⊗[F₂⊗F₁]
        ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
        ∘ᵥ associator.from)
        ∘ᵥ actionʳ₃ ◁ F₂ ◁ F₁
        ∘ᵥ associator.to ◁ F₁
        ∘ᵥ associator.to ≈⟨ hexagon ⟩∘⟨refl ⟩

      (α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁)
        ∘ᵥ actionʳ₃ ◁ F₂ ◁ F₁
        ∘ᵥ associator.to ◁ F₁
        ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩

      ((α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁)
        ∘ᵥ actionʳ₃ ◁ F₂ ◁ F₁
        ∘ᵥ associator.to ◁ F₁
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      ((α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁)
        ∘ᵥ (actionʳ₃ ◁ F₂ ◁ F₁
        ∘ᵥ associator.to ◁ F₁)
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      ((α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁)
        ∘ᵥ (actionʳ₃ ◁ F₂
        ∘ᵥ associator.to) ◁ F₁
        ∘ᵥ associator.to ≈⟨ assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ (actionʳ₃ ◁ F₂
        ∘ᵥ associator.to) ◁ F₁
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ (Coequalizer.arr F₃⊗F₂ ◁ F₁
        ∘ᵥ (actionʳ₃ ◁ F₂
        ∘ᵥ associator.to) ◁ F₁)
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      (α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ (Coequalizer.arr F₃⊗F₂
        ∘ᵥ actionʳ₃ ◁ F₂
        ∘ᵥ associator.to) ◁ F₁
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ ◁-resp-≈
                            actionʳSqF₂⊗F₁ ⟩∘⟨refl ⟩

      (α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ (Bimodule.actionʳ (B₃ ⊗₀ B₂)
        ∘ᵥ T₄ ▷ Coequalizer.arr F₃⊗F₂) ◁ F₁
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩

      (α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ (Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F₁
        ∘ᵥ (T₄ ▷ Coequalizer.arr F₃⊗F₂) ◁ F₁)
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F₁
        ∘ᵥ (T₄ ▷ Coequalizer.arr F₃⊗F₂) ◁ F₁
        ∘ᵥ associator.to ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ α⇐-▷-◁ ⟩

      (α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F₁
        ∘ᵥ associator.to
        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁) ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ (Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F₁
        ∘ᵥ associator.to)
        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁) ≈⟨ assoc₂ ⟩

      α⇒⊗
        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ (Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F₁
        ∘ᵥ associator.to)
        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁) ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

      α⇒⊗
        ∘ᵥ (Coequalizer.arr [F₃⊗F₂]⊗F₁
        ∘ᵥ Bimodule.actionʳ (B₃ ⊗₀ B₂) ◁ F₁
        ∘ᵥ associator.to)
        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁) ≈⟨ refl⟩∘⟨
                                                actionʳSq[F₃⊗F₂]⊗F₁
                                              ⟩∘⟨refl ⟩

      α⇒⊗
        ∘ᵥ (Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
        ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁) ≈⟨ sym-assoc₂ ⟩

      (α⇒⊗
        ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
        ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁) ≈⟨ sym-assoc₂ ⟩∘⟨refl ⟩

      ((α⇒⊗
        ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
        ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁)
        ∘ᵥ T₄ ▷ (Coequalizer.arr F₃⊗F₂ ◁ F₁) ∎

      where
        open hom.HomReasoning
        open TensorproductOfBimodules.Right-Action B₃ (B₂ ⊗₀ B₁)
          using () renaming (actionʳSq to actionʳSqF₃⊗[F₂⊗F₁])
        open TensorproductOfBimodules.Right-Action B₃ B₂
          using () renaming (actionʳSq to actionʳSqF₂⊗F₁)
        open TensorproductOfBimodules.Right-Action (B₃ ⊗₀ B₂) B₁
          using () renaming (actionʳSq to actionʳSq[F₃⊗F₂]⊗F₁)

    linearʳ∘arr : (Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                    ∘ᵥ T₄ ▷ α⇒⊗)
                    ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁
                  ≈ (α⇒⊗
                    ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                    ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁
    linearʳ∘arr = Coequalizer⇒Epi
                    (postcompCoequalizer (precompCoequalizer F₃⊗F₂ F₁) T₄)
                    ((Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
                      ∘ᵥ T₄ ▷ α⇒⊗)
                      ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁)
                    ((α⇒⊗
                      ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                      ∘ᵥ T₄ ▷ Coequalizer.arr [F₃⊗F₂]⊗F₁)
                    linearʳ∘arr∘arr

    linearʳ : Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁)
              ∘ᵥ T₄ ▷ α⇒⊗
              ≈ α⇒⊗
              ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁)
    linearʳ = Coequalizer⇒Epi
                (postcompCoequalizer [F₃⊗F₂]⊗F₁ T₄)
                (Bimodule.actionʳ (B₃ ⊗₀ B₂ ⊗₀ B₁) ∘ᵥ T₄ ▷ α⇒⊗)
                (α⇒⊗ ∘ᵥ Bimodule.actionʳ ((B₃ ⊗₀ B₂) ⊗₀ B₁))
                linearʳ∘arr
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
Associator⊗ = 2cellisIso⇒Iso Associator⊗From α⇒⊗isIso
  where
    open Bimodulehom-isIso
    α⇒⊗isIso : Categories.Morphism.IsIso (hom C₁ C₄) α⇒⊗
    α⇒⊗isIso = record
     { inv = _≅_.to 2-cell.Associator⊗Iso
     ; iso = _≅_.iso 2-cell.Associator⊗Iso
     }
