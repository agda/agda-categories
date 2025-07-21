{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism renaming (Bimodulehomomorphism to Bimodhom)


-- We will prove that the associator and unitor in the bicategory of monads and bimodules --
-- satisfies the triangle law. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Coherence.Triangle
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ : Monad 𝒞}
  {B₂ : Bimodule M₂ M₃} {B₁ : Bimodule M₁ M₂} where

import Categories.Bicategory.LocalCoequalizers
open ComposeWithLocalCoequalizer 𝒞 localCoeq
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct {o} {ℓ} {e} {t} {𝒞} {localCoeq}
private
  _⊗₀_ = TensorproductOfBimodules.B₂⊗B₁
  _⊗₁_ = TensorproductOfHomomorphisms.h₂⊗h₁
  
infixr 30 _⊗₀_ _⊗₁_

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞

import Categories.Diagram.Coequalizer
import Categories.Morphism
import Categories.Morphism.Reasoning.Iso

-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    open Categories.Morphism (hom X Y) public using (_≅_)
    open Categories.Diagram.Coequalizer (hom X Y) public
    open Categories.Morphism.Reasoning.Iso (hom X Y) public

open HomCat

open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator
  {𝒞 = 𝒞} {localCoeq}
  using (Associator⊗From; hexagon)
import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Unitor
  {𝒞 = 𝒞} {localCoeq} as Unitor
open Unitor.Left-Unitor using (Unitorˡ⊗From) renaming (triangle to left-unitor-triangle)
open Unitor.Right-Unitor using (Unitorʳ⊗From) renaming (triangle to right-unitor-triangle)

open TensorproductOfHomomorphisms using (αSq)

open Monad M₂ using () renaming (T to T₂)
open Bimodule B₁ using () renaming (F to F₁; actionʳ to actionʳ₁)
open Bimodule B₂ using () renaming (F to F₂; actionˡ to actionˡ₂)


open TensorproductOfBimodules B₂ B₁ using (F₂⊗F₁)
open TensorproductOfBimodules (id-bimodule M₂) B₁ using () renaming (F₂⊗F₁ to T₂⊗F₁)
open TensorproductOfBimodules B₂ (id-bimodule M₂) using () renaming (F₂⊗F₁ to F₂⊗T₂)
open TensorproductOfBimodules B₂ (id-bimodule M₂ ⊗₀ B₁) using () renaming (F₂⊗F₁ to F₂⊗[T₂⊗F₁])
open TensorproductOfBimodules (B₂ ⊗₀ id-bimodule M₂) B₁ using () renaming (F₂⊗F₁ to [F₂⊗T₂]⊗F₁)

abstract
  triangle⊗∘arr² : ((Bimodhom.α (id-bimodule-hom {B = B₂} ⊗₁ Unitorˡ⊗From {B = B₁})
                   ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₂} {id-bimodule M₂} {B₁}))
                   ∘ᵥ Coequalizer.arr [F₂⊗T₂]⊗F₁)
                   ∘ᵥ Coequalizer.arr F₂⊗T₂ ◁ F₁
                   ≈ (Bimodhom.α (Unitorʳ⊗From {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})
                     ∘ᵥ Coequalizer.arr [F₂⊗T₂]⊗F₁)
                     ∘ᵥ Coequalizer.arr F₂⊗T₂ ◁ F₁
  triangle⊗∘arr² = begin

    ((Bimodhom.α (id-bimodule-hom {B = B₂} ⊗₁ Unitorˡ⊗From {B = B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₂} {id-bimodule M₂} {B₁}))
    ∘ᵥ Coequalizer.arr [F₂⊗T₂]⊗F₁)
    ∘ᵥ Coequalizer.arr F₂⊗T₂ ◁ F₁
    ≈⟨ assoc₂ ⟩

    (Bimodhom.α (id-bimodule-hom {B = B₂} ⊗₁ Unitorˡ⊗From {B = B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₂} {id-bimodule M₂} {B₁}))
    ∘ᵥ Coequalizer.arr [F₂⊗T₂]⊗F₁
    ∘ᵥ Coequalizer.arr F₂⊗T₂ ◁ F₁
    ≈⟨ assoc₂ ⟩

    Bimodhom.α (id-bimodule-hom {B = B₂} ⊗₁ Unitorˡ⊗From {B = B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₂} {id-bimodule M₂} {B₁})
    ∘ᵥ Coequalizer.arr [F₂⊗T₂]⊗F₁
    ∘ᵥ Coequalizer.arr F₂⊗T₂ ◁ F₁
    ≈⟨ refl⟩∘⟨ ⟺ (hexagon {B₃ = B₂} {id-bimodule M₂} {B₁}) ⟩

    Bimodhom.α (id-bimodule-hom {B = B₂} ⊗₁ Unitorˡ⊗From {B = B₁})
    ∘ᵥ Coequalizer.arr F₂⊗[T₂⊗F₁]
    ∘ᵥ F₂ ▷ Coequalizer.arr T₂⊗F₁
    ∘ᵥ associator.from {f = F₂} {T₂} {F₁}
    ≈⟨ sym-assoc₂ ⟩

    (Bimodhom.α (id-bimodule-hom {B = B₂} ⊗₁ Unitorˡ⊗From {B = B₁})
    ∘ᵥ Coequalizer.arr F₂⊗[T₂⊗F₁])
    ∘ᵥ F₂ ▷ Coequalizer.arr T₂⊗F₁
    ∘ᵥ associator.from {f = F₂} {T₂} {F₁}
    ≈⟨ ⟺ (αSq (id-bimodule-hom {B = B₂}) (Unitorˡ⊗From {B = B₁})) ⟩∘⟨refl ⟩

    (Coequalizer.arr F₂⊗F₁
    ∘ᵥ F₂ ▷ Bimodhom.α (Unitorˡ⊗From {B = B₁}))
    ∘ᵥ F₂ ▷ Coequalizer.arr T₂⊗F₁
    ∘ᵥ associator.from {f = F₂} {T₂} {F₁}
    ≈⟨ assoc₂ ⟩

    Coequalizer.arr F₂⊗F₁
    ∘ᵥ F₂ ▷ Bimodhom.α (Unitorˡ⊗From {B = B₁})
    ∘ᵥ F₂ ▷ Coequalizer.arr T₂⊗F₁
    ∘ᵥ associator.from {f = F₂} {T₂} {F₁}
    ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

    Coequalizer.arr F₂⊗F₁
    ∘ᵥ (F₂ ▷ Bimodhom.α (Unitorˡ⊗From {B = B₁})
    ∘ᵥ F₂ ▷ Coequalizer.arr T₂⊗F₁)
    ∘ᵥ associator.from {f = F₂} {T₂} {F₁}
    ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩

    Coequalizer.arr F₂⊗F₁
    ∘ᵥ F₂ ▷ (Bimodhom.α (Unitorˡ⊗From {B = B₁})
            ∘ᵥ Coequalizer.arr T₂⊗F₁)
    ∘ᵥ associator.from {f = F₂} {T₂} {F₁}
    ≈⟨ refl⟩∘⟨ ▷-resp-≈ (left-unitor-triangle {B = B₁}) ⟩∘⟨refl ⟩

    Coequalizer.arr F₂⊗F₁
    ∘ᵥ F₂ ▷ actionʳ₁
    ∘ᵥ associator.from {f = F₂} {T₂} {F₁}
    ≈⟨ sym-assoc₂ ⟩

    (Coequalizer.arr F₂⊗F₁
    ∘ᵥ F₂ ▷ actionʳ₁)
    ∘ᵥ associator.from {f = F₂} {T₂} {F₁}
    ≈⟨ ⟺ (switch-tofromʳ associator F₂⊗F₁equality-var) ⟩

    Coequalizer.arr F₂⊗F₁
    ∘ᵥ actionˡ₂ ◁ F₁
    ≈⟨ refl⟩∘⟨ ◁-resp-≈ ( ⟺ (right-unitor-triangle {B = B₂})) ⟩

    Coequalizer.arr F₂⊗F₁
    ∘ᵥ (Bimodhom.α (Unitorʳ⊗From {B = B₂})
        ∘ᵥ Coequalizer.arr F₂⊗T₂) ◁ F₁
    ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩

    Coequalizer.arr F₂⊗F₁
    ∘ᵥ Bimodhom.α (Unitorʳ⊗From {B = B₂}) ◁ F₁
    ∘ᵥ Coequalizer.arr F₂⊗T₂ ◁ F₁
    ≈⟨ sym-assoc₂ ⟩

    (Coequalizer.arr F₂⊗F₁
    ∘ᵥ Bimodhom.α (Unitorʳ⊗From {B = B₂}) ◁ F₁)
    ∘ᵥ Coequalizer.arr F₂⊗T₂ ◁ F₁
    ≈⟨ αSq (Unitorʳ⊗From {B = B₂})(id-bimodule-hom {B = B₁}) ⟩∘⟨refl ⟩

    (Bimodhom.α (Unitorʳ⊗From {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})
    ∘ᵥ Coequalizer.arr [F₂⊗T₂]⊗F₁)
    ∘ᵥ Coequalizer.arr F₂⊗T₂ ◁ F₁ ∎

    where
      open hom.HomReasoning
      
      F₂⊗F₁equality-var : (Coequalizer.arr F₂⊗F₁
                          ∘ᵥ actionˡ₂ ◁ F₁)
                          ∘ᵥ associator.to {f = F₂} {T₂} {F₁}
                          ≈ Coequalizer.arr F₂⊗F₁
                            ∘ᵥ F₂ ▷ actionʳ₁
      F₂⊗F₁equality-var = begin
        (Coequalizer.arr F₂⊗F₁ ∘ᵥ actionˡ₂ ◁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ actionˡ₂ ◁ F₁ ∘ᵥ associator.to ≈⟨ ⟺ (Coequalizer.equality F₂⊗F₁) ⟩
        Coequalizer.arr F₂⊗F₁ ∘ᵥ F₂ ▷ actionʳ₁ ∎
  
  triangle⊗∘arr : (Bimodhom.α (id-bimodule-hom {B = B₂} ⊗₁ Unitorˡ⊗From {B = B₁})
                  ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₂} {id-bimodule M₂} {B₁}))
                  ∘ᵥ Coequalizer.arr [F₂⊗T₂]⊗F₁
                  ≈ Bimodhom.α (Unitorʳ⊗From {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})
                    ∘ᵥ Coequalizer.arr [F₂⊗T₂]⊗F₁
                    
  triangle⊗∘arr = Coequalizer⇒Epi
                    (F₂⊗T₂ coeq-◁ F₁)
                    ((Bimodhom.α (id-bimodule-hom ⊗₁ Unitorˡ⊗From)
                    ∘ᵥ Bimodhom.α Associator⊗From)
                    ∘ᵥ Coequalizer.arr [F₂⊗T₂]⊗F₁)
                    (Bimodhom.α (Unitorʳ⊗From ⊗₁ id-bimodule-hom)
                    ∘ᵥ Coequalizer.arr [F₂⊗T₂]⊗F₁)
                    triangle⊗∘arr²
  
  triangle⊗ : Bimodhom.α (id-bimodule-hom {B = B₂} ⊗₁ Unitorˡ⊗From {B = B₁})
              ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₂} {id-bimodule M₂} {B₁})
              ≈ Bimodhom.α (Unitorʳ⊗From {B = B₂} ⊗₁ id-bimodule-hom {B = B₁})

  triangle⊗ = Coequalizer⇒Epi
                [F₂⊗T₂]⊗F₁
                (Bimodhom.α (id-bimodule-hom ⊗₁ Unitorˡ⊗From)
                ∘ᵥ Bimodhom.α Associator⊗From)
                (Bimodhom.α (Unitorʳ⊗From ⊗₁ id-bimodule-hom))
                triangle⊗∘arr
