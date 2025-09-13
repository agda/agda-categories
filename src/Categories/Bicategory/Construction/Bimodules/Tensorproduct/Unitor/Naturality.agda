{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule renaming (Bimodulehomomorphism to Bimodhom)


-- We will show that the left- and right-unitor in the bicategory of monads and bimodules is natural. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Unitor.Naturality
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞}
  {M₁ M₂ : Monad 𝒞}
  {B B' : Bimodule M₁ M₂}
  (f : Bimodhom B B') where
  
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct {o} {ℓ} {e} {t} {𝒞} {localCoeq}

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
-- import Categories.Morphism

-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    -- open Categories.Morphism (hom X Y) public using (_≅_)
    open Categories.Diagram.Coequalizer (hom X Y) public
    open Categories.Diagram.Coequalizer.Properties (hom X Y) public

open HomCat

open Monad M₁ using () renaming (T to T₁)
open Monad M₂ using () renaming (T to T₂)

import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Unitor
  {o} {ℓ} {e} {t} {𝒞} {localCoeq} {M₁} {M₂} as Unitor

module Left-Unitor-natural where
  open Bimodule B using (actionʳ)
  open Bimodule B' using () renaming (actionʳ to actionʳ')
  open TensorproductOfBimodules Id-Bimod B using () renaming (F₂⊗F₁ to T₂⊗F)
  open TensorproductOfBimodules Id-Bimod B' using () renaming (F₂⊗F₁ to T₂⊗F')
  open Unitor.Left-Unitor using (λ⇒⊗; triangle)

  abstract
    λ⇒⊗-natural∘arr : (λ⇒⊗ {B'} ∘ᵥ Bimodhom.α (id-bimodule-hom ⊗₁ f)) ∘ᵥ Coequalizer.arr T₂⊗F
                      ≈ (Bimodhom.α f ∘ᵥ λ⇒⊗ {B}) ∘ᵥ Coequalizer.arr T₂⊗F
    λ⇒⊗-natural∘arr = begin
      (λ⇒⊗ {B'} ∘ᵥ Bimodhom.α (id-bimodule-hom ⊗₁ f)) ∘ᵥ Coequalizer.arr T₂⊗F ≈⟨ assoc₂ ⟩
      λ⇒⊗ {B'} ∘ᵥ Bimodhom.α (id-bimodule-hom ⊗₁ f) ∘ᵥ Coequalizer.arr T₂⊗F   ≈⟨ refl⟩∘⟨ ⟺ αSqid⊗f ⟩
      λ⇒⊗ {B'} ∘ᵥ Coequalizer.arr T₂⊗F' ∘ᵥ T₂ ▷ Bimodhom.α f                  ≈⟨ sym-assoc₂ ⟩
      (λ⇒⊗ {B'} ∘ᵥ Coequalizer.arr T₂⊗F') ∘ᵥ T₂ ▷ Bimodhom.α f                ≈⟨ triangle {B'} ⟩∘⟨refl ⟩
      actionʳ' ∘ᵥ T₂ ▷ Bimodhom.α f                                           ≈⟨ linearʳ ⟩
      Bimodhom.α f ∘ᵥ actionʳ                                                 ≈⟨ refl⟩∘⟨ ⟺ (triangle {B}) ⟩
      Bimodhom.α f ∘ᵥ λ⇒⊗ {B} ∘ᵥ Coequalizer.arr T₂⊗F                         ≈⟨ sym-assoc₂ ⟩
      (Bimodhom.α f ∘ᵥ λ⇒⊗ {B}) ∘ᵥ Coequalizer.arr T₂⊗F                       ∎
      where
        open hom.HomReasoning
        open Bimodhom f using (linearʳ)
        open TensorproductOfHomomorphisms id-bimodule-hom f using () renaming (αSq to αSqid⊗f)

    λ⇒⊗-natural : λ⇒⊗ {B'} ∘ᵥ Bimodhom.α (id-bimodule-hom ⊗₁ f) ≈ Bimodhom.α f ∘ᵥ λ⇒⊗ {B}
    λ⇒⊗-natural = Coequalizer⇒Epi
                    T₂⊗F
                    (λ⇒⊗ ∘ᵥ Bimodhom.α (id-bimodule-hom ⊗₁ f))
                    (Bimodhom.α f ∘ᵥ λ⇒⊗)
                    λ⇒⊗-natural∘arr

  -- end abstract --

module Right-Unitor-natural where
  open Bimodule B using (actionˡ)
  open Bimodule B' using () renaming (actionˡ to actionˡ')
  open TensorproductOfBimodules B Id-Bimod using () renaming (F₂⊗F₁ to F⊗T₁)
  open TensorproductOfBimodules B' Id-Bimod using () renaming (F₂⊗F₁ to F'⊗T₁)
  open Unitor.Right-Unitor using (ρ⇒⊗; triangle)

  abstract
    ρ⇒⊗-natural∘arr : (ρ⇒⊗ {B'} ∘ᵥ Bimodhom.α (f ⊗₁ id-bimodule-hom)) ∘ᵥ Coequalizer.arr F⊗T₁
                      ≈ (Bimodhom.α f ∘ᵥ ρ⇒⊗ {B}) ∘ᵥ Coequalizer.arr F⊗T₁
    ρ⇒⊗-natural∘arr = begin
      (ρ⇒⊗ {B'} ∘ᵥ Bimodhom.α (f ⊗₁ id-bimodule-hom)) ∘ᵥ Coequalizer.arr F⊗T₁ ≈⟨ assoc₂ ⟩
      ρ⇒⊗ {B'} ∘ᵥ Bimodhom.α (f ⊗₁ id-bimodule-hom) ∘ᵥ Coequalizer.arr F⊗T₁   ≈⟨ refl⟩∘⟨ ⟺ αSqf⊗id ⟩
      ρ⇒⊗ {B'} ∘ᵥ Coequalizer.arr F'⊗T₁ ∘ᵥ Bimodhom.α f ◁ T₁                   ≈⟨ sym-assoc₂ ⟩
      (ρ⇒⊗ {B'} ∘ᵥ Coequalizer.arr F'⊗T₁) ∘ᵥ Bimodhom.α f ◁ T₁                ≈⟨ triangle {B'} ⟩∘⟨refl ⟩
      actionˡ' ∘ᵥ Bimodhom.α f ◁ T₁                                           ≈⟨ linearˡ ⟩
      Bimodhom.α f ∘ᵥ actionˡ                                                 ≈⟨ refl⟩∘⟨ ⟺ (triangle {B}) ⟩
      Bimodhom.α f ∘ᵥ ρ⇒⊗ {B} ∘ᵥ Coequalizer.arr F⊗T₁                         ≈⟨ sym-assoc₂ ⟩
      (Bimodhom.α f ∘ᵥ ρ⇒⊗ {B}) ∘ᵥ Coequalizer.arr F⊗T₁                       ∎
      where
        open hom.HomReasoning
        open Bimodhom f using (linearˡ)
        open TensorproductOfHomomorphisms f id-bimodule-hom using () renaming (αSq to αSqf⊗id)

    ρ⇒⊗-natural : ρ⇒⊗ {B'} ∘ᵥ Bimodhom.α (f ⊗₁ id-bimodule-hom) ≈ Bimodhom.α f ∘ᵥ ρ⇒⊗ {B}
    ρ⇒⊗-natural = Coequalizer⇒Epi
                    F⊗T₁
                    (ρ⇒⊗ ∘ᵥ Bimodhom.α (f ⊗₁ id-bimodule-hom))
                    (Bimodhom.α f ∘ᵥ ρ⇒⊗)
                    ρ⇒⊗-natural∘arr

  -- end abstract --
