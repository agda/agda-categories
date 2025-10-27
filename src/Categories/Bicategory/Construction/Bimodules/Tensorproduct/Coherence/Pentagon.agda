{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule


-- We will prove that the associator in the bicategory of monads and bimodules --
-- satisfies the pentagon law. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Coherence.Pentagon
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ M₄ M₅ : Monad 𝒞}
  {B₄ : Bimodule M₄ M₅} {B₃ : Bimodule M₃ M₄} {B₂ : Bimodule M₂ M₃} {B₁ : Bimodule M₁ M₂} where

import Categories.Bicategory.LocalCoequalizers
open ComposeWithLocalCoequalizer 𝒞 localCoeq

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands

open Bimodule using (F)
open import Categories.Bicategory.Monad.Bimodule.Homomorphism
open Bimodulehomomorphism using (α)

import Categories.Diagram.Coequalizer
import Categories.Morphism

-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    open Categories.Morphism (hom X Y) public using (_≅_)
    open Categories.Diagram.Coequalizer (hom X Y) using (Coequalizer; Coequalizer⇒Epi) public
    open Coequalizer using (obj; arr) public

open HomCat

import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} as TensorproductOfBimodules
import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq} as TensorproductOfHomomorphisms
open TensorproductOfBimodules using (CoeqBimods) renaming (Tensorproduct to infixr 30 _⊗₀_)
open TensorproductOfHomomorphisms using () renaming (Tensorproduct to infixr 30 _⊗₁_)
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator {𝒞 = 𝒞} {localCoeq}
  using (associator-⊗-from; hexagon)

abstract
  -- We reduce the pentagon law for the tensorproduct to the pentagon law in 𝒞 --
  -- For this, we consider a prism with the following five faces. --

  face[[43]2]1⇒[43]21 : α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
                        ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
                        ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
                        ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
                        ≈ (arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
                          ∘ᵥ F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁)
                          ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ (F B₂ ∘₁ F B₁))
                          ∘ᵥ α⇒ {f = F B₄ ∘₁ F B₃} {F B₂} {F B₁}
  face[[43]2]1⇒[43]21 = begin

    α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

    (α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

    ((α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁)
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁)
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ ⟺ (hexagon {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}) ⟩∘⟨refl ⟩

    (arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ α⇒ {f = F (B₄ ⊗₀ B₃)} {F B₂} {F B₁})
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ assoc₂ ⟩

    arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ (F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ α⇒ {f = F (B₄ ⊗₀ B₃)} {F B₂} {F B₁})
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ refl⟩∘⟨ assoc₂ ⟩

    arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ α⇒ {f = F (B₄ ⊗₀ B₃)} {F B₂} {F B₁}
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-◁-∘₁ ⟩

    arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ (F B₂ ∘₁ F B₁)
    ∘ᵥ α⇒ {f = F B₄ ∘₁ F B₃} {F B₂} {F B₁}
    ≈⟨ sym-assoc₂ ⟩

    (arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ (F B₂ ∘₁ F B₁)
    ∘ᵥ α⇒ {f = F B₄ ∘₁ F B₃} {F B₂} {F B₁}
    ≈⟨ sym-assoc₂ ⟩

    ((arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ (F B₂ ∘₁ F B₁))
    ∘ᵥ α⇒ {f = F B₄ ∘₁ F B₃} {F B₂} {F B₁}
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ (F B₂ ∘₁ F B₁))
    ∘ᵥ α⇒ {f = F B₄ ∘₁ F B₃} {F B₂} {F B₁} ∎

    where
      open hom.HomReasoning

  face[43]21⇒4321 : α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
                    ∘ᵥ F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁)
                    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ (F B₂ ∘₁ F B₁)
                    ≈ (arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
                      ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
                      ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
                      ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂ ∘₁ F B₁}
  face[43]21⇒4321 = begin

    α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ (F B₂ ∘₁ F B₁)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ◁-▷-exchg ⟩

    α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F (B₂ ⊗₀ B₁)
    ∘ᵥ (F B₄ ∘₁ F B₃) ▷ arr (CoeqBimods B₂ B₁)
    ≈⟨ sym-assoc₂ ⟩

    (α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁)))
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F (B₂ ⊗₀ B₁)
    ∘ᵥ (F B₄ ∘₁ F B₃) ▷ arr (CoeqBimods B₂ B₁)
    ≈⟨ sym-assoc₂ ⟩

    ((α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁)))
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F (B₂ ⊗₀ B₁))
    ∘ᵥ (F B₄ ∘₁ F B₃) ▷ arr (CoeqBimods B₂ B₁)
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F (B₂ ⊗₀ B₁))
    ∘ᵥ (F B₄ ∘₁ F B₃) ▷ arr (CoeqBimods B₂ B₁)
    ≈⟨ ⟺ (hexagon {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁}) ⟩∘⟨refl ⟩

    (arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F (B₂ ⊗₀ B₁)})
    ∘ᵥ (F B₄ ∘₁ F B₃) ▷ arr (CoeqBimods B₂ B₁)
    ≈⟨ assoc₂ ⟩

    arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F (B₂ ⊗₀ B₁)})
    ∘ᵥ (F B₄ ∘₁ F B₃) ▷ arr (CoeqBimods B₂ B₁)
    ≈⟨ refl⟩∘⟨ assoc₂ ⟩

    arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F (B₂ ⊗₀ B₁)}
    ∘ᵥ (F B₄ ∘₁ F B₃) ▷ arr (CoeqBimods B₂ B₁)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-▷-∘₁ ⟩

    arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂ ∘₁ F B₁}
    ≈⟨ sym-assoc₂ ⟩

    (arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)))
    ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂ ∘₁ F B₁}
    ≈⟨ sym-assoc₂ ⟩

    ((arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)))
    ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂ ∘₁ F B₁}
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂ ∘₁ F B₁} ∎

    where
      open hom.HomReasoning

  face[[43]2]1⇒[432]1 : α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁})
                        ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
                        ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
                        ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
                        ≈ (arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
                          ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁
                          ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁)
                          ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁
  face[[43]2]1⇒[432]1 = begin

    α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁})
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

    (α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁})
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ ⟺ αSq-⊗ ⟩∘⟨refl ⟩

    (arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂}) ◁ F B₁)
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ assoc₂ ⟩

    arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂}) ◁ F B₁
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩

    arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂}) ◁ F B₁
    ∘ᵥ (arr (CoeqBimods (B₄ ⊗₀ B₃) B₂)
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂) ◁ F B₁
    ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩

    arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ (α (associator-⊗-from {B₃ = B₄} {B₃} {B₂})
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂)
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂) ◁ F B₁
    ≈⟨ refl⟩∘⟨ ◁-resp-≈ (⟺ (hexagon {B₃ = B₄} {B₃} {B₂})) ⟩

    arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ (arr (CoeqBimods B₄ (B₃ ⊗₀ B₂))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ B₂)
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂}) ◁ F B₁
    ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩

    arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂}) ◁ F B₁
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩

    arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

    (arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁)
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

    ((arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁)
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁)
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁)
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁ ∎

    where
      open hom.HomReasoning
      open TensorproductOfHomomorphisms (associator-⊗-from {B₃ = B₄} {B₃} {B₂}) (id-bimodule-hom {B = B₁}) using (αSq-⊗)

  face[432]1⇒4[32]1 : α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                      ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
                      ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁
                      ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
                      ≈ (arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
                        ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                        ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁))
                        ∘ᵥ α⇒ {f = F B₄} {F B₃ ∘₁ F B₂} {F B₁}
  face[432]1⇒4[32]1 = begin

    α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

    (α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

    ((α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁)
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁)
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
    ≈⟨ ⟺ (hexagon {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁}) ⟩∘⟨refl ⟩

    (arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ α⇒ {f = F B₄} {F (B₃ ⊗₀ B₂)} {F B₁})
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
    ≈⟨ assoc₂ ⟩

    arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ α⇒ {f = F B₄} {F (B₃ ⊗₀ B₂)} {F B₁})
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
    ≈⟨ refl⟩∘⟨ assoc₂ ⟩

    arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ α⇒ {f = F B₄} {F (B₃ ⊗₀ B₂)} {F B₁}
    ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-▷-◁ ⟩

    arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
    ∘ᵥ α⇒ {f = F B₄} {F B₃ ∘₁ F B₂} {F B₁}
    ≈⟨ sym-assoc₂ ⟩

    (arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
    ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
    ∘ᵥ α⇒ {f = F B₄} {F B₃ ∘₁ F B₂} {F B₁}
    ≈⟨ sym-assoc₂ ⟩

    ((arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
    ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁))
    ∘ᵥ α⇒ {f = F B₄} {F B₃ ∘₁ F B₂} {F B₁}
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁))
    ∘ᵥ α⇒ {f = F B₄} {F B₃ ∘₁ F B₂} {F B₁} ∎

    where
      open hom.HomReasoning

  face4[32]1⇒4321 : α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
                    ∘ᵥ arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
                    ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                    ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
                    ≈ (arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
                      ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
                      ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
                      ∘ᵥ F B₄ ▷ α⇒ {f = F B₃} {F B₂} {F B₁}
  face4[32]1⇒4321 = begin

    α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
    ≈⟨ sym-assoc₂ ⟩

    (α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁)))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
    ≈⟨ ⟺ αSq-⊗ ⟩∘⟨refl ⟩

    (arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ α (associator-⊗-from {B₃ = B₃} {B₂} {B₁}))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
    ≈⟨ assoc₂ ⟩

    arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ α (associator-⊗-from {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩

    arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ α (associator-⊗-from {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ F B₄ ▷ (arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
             ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
    ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩

    arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ (α (associator-⊗-from {B₃ = B₃} {B₂} {B₁})
             ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
             ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F B₁)
    ≈⟨ refl⟩∘⟨ ▷-resp-≈ (⟺ (hexagon {B₃ = B₃} {B₂} {B₁})) ⟩

    arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
             ∘ᵥ F B₃ ▷ arr (CoeqBimods B₂ B₁)
             ∘ᵥ α⇒ {f = F B₃} {F B₂} {F B₁})
    ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩

    arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ (F B₃ ▷ arr (CoeqBimods B₂ B₁)
             ∘ᵥ α⇒ {f = F B₃} {F B₂} {F B₁})
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩

    arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ F B₄ ▷ α⇒ {f = F B₃} {F B₂} {F B₁}
    ≈⟨ sym-assoc₂ ⟩

    (arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)))
    ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ F B₄ ▷ α⇒ {f = F B₃} {F B₂} {F B₁}
    ≈⟨ sym-assoc₂ ⟩

    ((arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)))
    ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ F B₄ ▷ α⇒ {f = F B₃} {F B₂} {F B₁}
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ F B₄ ▷ α⇒ {f = F B₃} {F B₂} {F B₁} ∎

    where
      open hom.HomReasoning
      open TensorproductOfHomomorphisms (id-bimodule-hom {B = B₄}) (associator-⊗-from {B₃ = B₃} {B₂} {B₁}) using (αSq-⊗)

abstract
  pentagon-⊗-∘arr³ : (((α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
                   ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                   ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
                   ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                   ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁)
                   ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
                   ≈ (((α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                     ∘ᵥ α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
                     ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                     ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁)
                     ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁

  pentagon-⊗-∘arr³ = begin

    (((α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁)
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ assoc₂ ⟩

    ((α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ assoc₂ ⟩

    (α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ assoc₂ ⟩

    α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ (α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ refl⟩∘⟨ assoc₂ ⟩

    α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
      ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁})
      ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
      ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
      ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ face[[43]2]1⇒[432]1 ⟩

    α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
      ∘ᵥ (arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
      ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁
      ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁)
      ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁
    ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

    α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
      ∘ᵥ (α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
      ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
      ∘ᵥ arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F B₁
      ∘ᵥ (F B₄ ▷ arr (CoeqBimods B₃ B₂)) ◁ F B₁)
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁
    ≈⟨ refl⟩∘⟨ face[432]1⇒4[32]1 ⟩∘⟨refl ⟩

    α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
      ∘ᵥ ((arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
      ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁))
      ∘ᵥ α⇒ {f = F B₄} {F B₃ ∘₁ F B₂} {F B₁})
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁
    ≈⟨ refl⟩∘⟨ assoc₂ ⟩

    α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
      ∘ᵥ (arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
      ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁))
    ∘ᵥ α⇒ {f = F B₄} {F B₃ ∘₁ F B₂} {F B₁}
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

      (α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
      ∘ᵥ arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
      ∘ᵥ F B₄ ▷ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ F B₄ ▷ (arr (CoeqBimods B₃ B₂) ◁ F B₁))
    ∘ᵥ α⇒ {f = F B₄} {F B₃ ∘₁ F B₂} {F B₁}
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁
    ≈⟨ face4[32]1⇒4321 ⟩∘⟨refl ⟩

      ((arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
      ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
      ∘ᵥ F B₄ ▷ α⇒ {f = F B₃} {F B₂} {F B₁})
    ∘ᵥ α⇒ {f = F B₄} {F B₃ ∘₁ F B₂} {F B₁}
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁
    ≈⟨ assoc₂ ⟩

      (arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
      ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ F B₄ ▷ α⇒ {f = F B₃} {F B₂} {F B₁}
    ∘ᵥ α⇒ {f = F B₄} {F B₃ ∘₁ F B₂} {F B₁}
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂} ◁ F B₁
    ≈⟨ refl⟩∘⟨ pentagon ⟩

      (arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
      ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂ ∘₁ F B₁}
    ∘ᵥ α⇒ {f = F B₄ ∘₁ F B₃} {F B₂} {F B₁}
    ≈⟨ sym-assoc₂ ⟩

      ((arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
      ∘ᵥ F B₄ ▷ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F B₄ ▷ F B₃ ▷ arr (CoeqBimods B₂ B₁))
      ∘ᵥ α⇒ {f = F B₄} {F B₃} {F B₂ ∘₁ F B₁})
    ∘ᵥ α⇒ {f = F B₄ ∘₁ F B₃} {F B₂} {F B₁}
    ≈⟨ ⟺ face[43]21⇒4321 ⟩∘⟨refl ⟩

      (α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
      ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
      ∘ᵥ F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ (F B₂ ∘₁ F B₁))
    ∘ᵥ α⇒ {f = F B₄ ∘₁ F B₃} {F B₂} {F B₁}
    ≈⟨ assoc₂ ⟩

    α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
      ∘ᵥ (arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
      ∘ᵥ F (B₄ ⊗₀ B₃) ▷ arr (CoeqBimods B₂ B₁)
      ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ (F B₂ ∘₁ F B₁))
      ∘ᵥ α⇒ {f = F B₄ ∘₁ F B₃} {F B₂} {F B₁}
    ≈⟨ refl⟩∘⟨ ⟺ face[[43]2]1⇒[43]21 ⟩

    α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
      ∘ᵥ α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
      ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
      ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
      ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

    (α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

    ((α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

    (((α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁)
    ∘ᵥ arr (CoeqBimods B₄ B₃) ◁ F B₂ ◁ F B₁ ∎

    where
      open hom.HomReasoning

abstract
  pentagon-⊗-∘arr² : ((α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
                   ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                   ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
                   ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                   ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
                   ≈ ((α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                     ∘ᵥ α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
                     ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                     ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁
  pentagon-⊗-∘arr² = Coequalizer⇒Epi

                     ((CoeqBimods B₄ B₃) coeq-◁ F B₂ coeq-◁ F B₁)

                     (((α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
                     ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                     ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
                     ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                     ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁)

                     (((α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                     ∘ᵥ α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
                     ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                     ∘ᵥ arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F B₁)

                     pentagon-⊗-∘arr³

abstract
  pentagon-⊗-∘arr : (α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
                  ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                  ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
                  ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
                   ≈ (α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                     ∘ᵥ α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
                     ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
  pentagon-⊗-∘arr = Coequalizer⇒Epi

                    ((CoeqBimods (B₄ ⊗₀ B₃) B₂) coeq-◁ F B₁)

                    ((α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
                    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                    ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
                    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))

                    ((α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                    ∘ᵥ α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
                    ∘ᵥ arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))

                    pentagon-⊗-∘arr²

abstract
  pentagon-⊗ : α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
              ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
              ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁})
              ≈ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                ∘ᵥ α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
  pentagon-⊗ = Coequalizer⇒Epi

                (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)

                (α (id-bimodule-hom {B = B₄} ⊗₁ associator-⊗-from {B₃ = B₃} {B₂} {B₁})
                ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                ∘ᵥ α (associator-⊗-from {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))

                (α (associator-⊗-from {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                ∘ᵥ α (associator-⊗-from {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))

                pentagon-⊗-∘arr
