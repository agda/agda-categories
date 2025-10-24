{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism


-- We will prove that the associator and unitor in the bicategory of monads and bimodules --
-- satisfies the triangle law. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Coherence.Triangle
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ : Monad 𝒞}
  {B₂ : Bimodule M₂ M₃} {B₁ : Bimodule M₁ M₂} where

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands

import Categories.Bicategory.LocalCoequalizers
open ComposeWithLocalCoequalizer 𝒞 localCoeq

open Monad using (T)
open Bimodule using (F; actionˡ; actionʳ)
open Bimodulehomomorphism using (α)

import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} as TensorproductOfBimodules
import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq} as TensorproductOfHomomorphisms
open TensorproductOfBimodules using () renaming (Tensorproduct to infixr 30 _⊗₀_)
open TensorproductOfHomomorphisms using () renaming (Tensorproduct to infixr 30 _⊗₁_)

Id-Bimod : {M : Monad 𝒞} → Bimodule M M
Id-Bimod {M} = id-bimodule M

import Categories.Diagram.Coequalizer
import Categories.Morphism
import Categories.Morphism.Reasoning.Iso

-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    open Categories.Morphism (hom X Y) public using (_≅_)
    open Categories.Diagram.Coequalizer (hom X Y) public
    open Coequalizer using (arr; equality) public
    open Categories.Morphism.Reasoning.Iso (hom X Y) public

open HomCat

open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator
  {𝒞 = 𝒞} {localCoeq}
  using (associator-⊗-from; hexagon)
import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Unitor
  {𝒞 = 𝒞} {localCoeq} as Unitor
open Unitor.Left-Unitor using (unitorˡ-⊗-from) renaming (triangle to left-unitor-triangle)
open Unitor.Right-Unitor using (unitorʳ-⊗-from) renaming (triangle to right-unitor-triangle)

open TensorproductOfBimodules using (CoeqBimods)
open TensorproductOfHomomorphisms using (αSq-⊗)

abstract
  triangle⊗∘arr² : ((α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
                   ∘ᵥ α (associator-⊗-from {B₃ = B₂} {Id-Bimod} {B₁}))
                   ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
                   ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
                   ≈ (α (unitorʳ-⊗-from {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})
                     ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
                     ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
  triangle⊗∘arr² = begin

    ((α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₂} {Id-Bimod} {B₁}))
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
    ≈⟨ assoc₂ ⟩

    (α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₂} {Id-Bimod} {B₁}))
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁)
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
    ≈⟨ assoc₂ ⟩

    α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
    ∘ᵥ α (associator-⊗-from {B₃ = B₂} {Id-Bimod} {B₁})
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁)
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
    ≈⟨ refl⟩∘⟨ ⟺ (hexagon {B₃ = B₂} {Id-Bimod} {B₁}) ⟩

    α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
    ∘ᵥ arr (CoeqBimods B₂ (Id-Bimod ⊗₀ B₁))
    ∘ᵥ F B₂ ▷ arr (CoeqBimods Id-Bimod B₁)
    ∘ᵥ α⇒ {f = F B₂} {T M₂} {F B₁}
    ≈⟨ sym-assoc₂ ⟩

    (α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
    ∘ᵥ arr (CoeqBimods B₂ (Id-Bimod ⊗₀ B₁)))
    ∘ᵥ F B₂ ▷ arr (CoeqBimods Id-Bimod B₁)
    ∘ᵥ α⇒ {f = F B₂} {T M₂} {F B₁}
    ≈⟨ ⟺ (αSq-⊗ (id-bimodule-hom {B = B₂}) (unitorˡ-⊗-from {B = B₁})) ⟩∘⟨refl ⟩

    (arr (CoeqBimods B₂ B₁)
    ∘ᵥ F B₂ ▷ α (unitorˡ-⊗-from {B = B₁}))
    ∘ᵥ F B₂ ▷ arr (CoeqBimods Id-Bimod B₁)
    ∘ᵥ α⇒ {f = F B₂} {T M₂} {F B₁}
    ≈⟨ assoc₂ ⟩

    arr (CoeqBimods B₂ B₁)
    ∘ᵥ F B₂ ▷ α (unitorˡ-⊗-from {B = B₁})
    ∘ᵥ F B₂ ▷ arr (CoeqBimods Id-Bimod B₁)
    ∘ᵥ α⇒ {f = F B₂} {T M₂} {F B₁}
    ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

    arr (CoeqBimods B₂ B₁)
    ∘ᵥ (F B₂ ▷ α (unitorˡ-⊗-from {B = B₁})
    ∘ᵥ F B₂ ▷ arr (CoeqBimods Id-Bimod B₁))
    ∘ᵥ α⇒ {f = F B₂} {T M₂} {F B₁}
    ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

    arr (CoeqBimods B₂ B₁)
    ∘ᵥ F B₂ ▷ (α (unitorˡ-⊗-from {B = B₁})
            ∘ᵥ arr (CoeqBimods Id-Bimod B₁))
    ∘ᵥ α⇒ {f = F B₂} {T M₂} {F B₁}
    ≈⟨ refl⟩∘⟨ ▷-resp-≈ (left-unitor-triangle {B = B₁}) ⟩∘⟨refl ⟩

    arr (CoeqBimods B₂ B₁)
    ∘ᵥ F B₂ ▷ actionʳ B₁
    ∘ᵥ α⇒ {f = F B₂} {T M₂} {F B₁}
    ≈⟨ sym-assoc₂ ⟩

    (arr (CoeqBimods B₂ B₁)
    ∘ᵥ F B₂ ▷ actionʳ B₁)
    ∘ᵥ α⇒ {f = F B₂} {T M₂} {F B₁}
    ≈⟨ ⟺ (switch-tofromʳ associator F₂⊗F₁equality-var) ⟩

    arr (CoeqBimods B₂ B₁)
    ∘ᵥ actionˡ B₂ ◁ F B₁
    ≈⟨ refl⟩∘⟨ ◁-resp-≈ ( ⟺ (right-unitor-triangle {B = B₂})) ⟩

    arr (CoeqBimods B₂ B₁)
    ∘ᵥ (α (unitorʳ-⊗-from {B = B₂})
        ∘ᵥ arr (CoeqBimods B₂ Id-Bimod)) ◁ F B₁
    ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩

    arr (CoeqBimods B₂ B₁)
    ∘ᵥ α (unitorʳ-⊗-from {B = B₂}) ◁ F B₁
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
    ≈⟨ sym-assoc₂ ⟩

    (arr (CoeqBimods B₂ B₁)
    ∘ᵥ α (unitorʳ-⊗-from {B = B₂}) ◁ F B₁)
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁
    ≈⟨ αSq-⊗ (unitorʳ-⊗-from {B = B₂}) (id-bimodule-hom {B = B₁}) ⟩∘⟨refl ⟩

    (α (unitorʳ-⊗-from {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})
    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
    ∘ᵥ arr (CoeqBimods B₂ Id-Bimod) ◁ F B₁ ∎

    where
      open hom.HomReasoning
      
      F₂⊗F₁equality-var : (arr (CoeqBimods B₂ B₁)
                          ∘ᵥ actionˡ B₂ ◁ F B₁)
                          ∘ᵥ α⇐ {f = F B₂} {T M₂} {F B₁}
                          ≈ arr (CoeqBimods B₂ B₁)
                            ∘ᵥ F B₂ ▷ actionʳ B₁
      F₂⊗F₁equality-var = begin
        (arr (CoeqBimods B₂ B₁) ∘ᵥ actionˡ B₂ ◁ F B₁) ∘ᵥ α⇐ ≈⟨ assoc₂ ⟩
        arr (CoeqBimods B₂ B₁) ∘ᵥ actionˡ B₂ ◁ F B₁ ∘ᵥ α⇐ ≈⟨ ⟺ (equality (CoeqBimods B₂ B₁)) ⟩
        arr (CoeqBimods B₂ B₁) ∘ᵥ F B₂ ▷ actionʳ B₁ ∎

  triangle⊗∘arr : (α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
                  ∘ᵥ α (associator-⊗-from {B₃ = B₂} {Id-Bimod} {B₁}))
                  ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁)
                  ≈ α (unitorʳ-⊗-from {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})
                    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁)
                    
  triangle⊗∘arr = Coequalizer⇒Epi
                    ((CoeqBimods B₂ Id-Bimod) coeq-◁ F B₁)
                    ((α (id-bimodule-hom ⊗₁ unitorˡ-⊗-from)
                    ∘ᵥ α associator-⊗-from)
                    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
                    (α (unitorʳ-⊗-from ⊗₁ id-bimodule-hom)
                    ∘ᵥ arr (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁))
                    triangle⊗∘arr²
  
  triangle⊗ : α (id-bimodule-hom {B = B₂} ⊗₁ unitorˡ-⊗-from {B = B₁})
              ∘ᵥ α (associator-⊗-from {B₃ = B₂} {Id-Bimod} {B₁})
              ≈ α (unitorʳ-⊗-from {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})

  triangle⊗ = Coequalizer⇒Epi
                (CoeqBimods (B₂ ⊗₀ Id-Bimod) B₁)
                (α (id-bimodule-hom ⊗₁ unitorˡ-⊗-from)
                ∘ᵥ α associator-⊗-from)
                (α (unitorʳ-⊗-from ⊗₁ id-bimodule-hom))
                triangle⊗∘arr
