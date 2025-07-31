{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism renaming (Bimodulehomomorphism to Bimodhom)


-- We will prove that the associator in the bicategory of monads and bimodules --
-- satisfies the pentagon law. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Coherence.Pentagon
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ M₄ M₅ : Monad 𝒞}
  {B₄ : Bimodule M₄ M₅} {B₃ : Bimodule M₃ M₄} {B₂ : Bimodule M₂ M₃} {B₁ : Bimodule M₁ M₂} where

import Categories.Bicategory.LocalCoequalizers
open ComposeWithLocalCoequalizer 𝒞 localCoeq
import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} as TensorproductOfBimodules
import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq} as TensorproductOfHomomorphisms
private
  _⊗₀_ = TensorproductOfBimodules.B₂⊗B₁
  _⊗₁_ = TensorproductOfHomomorphisms.h₂⊗h₁
  
infixr 30 _⊗₀_ _⊗₁_

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞

import Categories.Diagram.Coequalizer
import Categories.Morphism

-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    open Categories.Morphism (hom X Y) public using (_≅_)
    open Categories.Diagram.Coequalizer (hom X Y) public

open HomCat

open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator
  {𝒞 = 𝒞} {localCoeq}
  using (Associator⊗From; hexagon)

open TensorproductOfBimodules using (CoeqBimods)
open TensorproductOfHomomorphisms using (αSq)

open Bimodule B₁ using () renaming (F to F₁)
open Bimodule B₂ using () renaming (F to F₂)
open Bimodule B₃ using () renaming (F to F₃)
open Bimodule B₄ using () renaming (F to F₄)
-- open TensorproductOfBimodules B₂ B₁ using (F₂⊗F₁)
-- open TensorproductOfBimodules B₃ B₂ using () renaming (F₂⊗F₁ to F₃⊗F₂)
-- open TensorproductOfBimodules B₄ B₃ using () renaming (F₂⊗F₁ to F₄⊗F₃)
-- open TensorproductOfBimodules B₃ (B₂ ⊗₀ B₁) using () renaming (F₂⊗F₁ to F₃⊗F₂⊗F₁)
-- open TensorproductOfBimodules (B₃ ⊗₀ B₂) B₁ using () renaming (F₂⊗F₁ to [F₃⊗F₂]⊗F₁)
-- open TensorproductOfBimodules (B₄ ⊗₀ B₃) B₂ using () renaming (F₂⊗F₁ to [F₄⊗F₃]⊗F₂ )
-- open TensorproductOfBimodules B₄ (B₃ ⊗₀ B₂) using () renaming (F₂⊗F₁ to F₄⊗F₃⊗F₂ )
-- open TensorproductOfBimodules ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁ using () renaming (F₂⊗F₁ to [[F₄⊗F₃]⊗F₂]⊗F₁)
-- open TensorproductOfBimodules (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁) using () renaming (F₂⊗F₁ to [F₄⊗F₃]⊗F₂⊗F₁)
-- open TensorproductOfBimodules (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁ using () renaming (F₂⊗F₁ to [F₄⊗F₃⊗F₂]⊗F₁)
-- open TensorproductOfBimodules B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁) using () renaming (F₂⊗F₁ to F₄⊗[F₃⊗F₂]⊗F₁)


abstract
  -- We reduce the pentagon law for the tensorproduct to the pentagon law in 𝒞 --
  -- For this, we consider a prism with the following five faces. --

  face[[43]2]1⇒[43]21 : Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
                        ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
                        ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
                        ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
                        ≈ (Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
                          ∘ᵥ Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
                          ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ (F₂ ∘₁ F₁))
                          ∘ᵥ associator.from {f = F₄ ∘₁ F₃} {F₂} {F₁}
  face[[43]2]1⇒[43]21 = begin
  
    Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ sym-assoc₂ ⟩
  
    (Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ sym-assoc₂ ⟩
  
    ((Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩
  
    (Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ ⟺ (hexagon {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}) ⟩∘⟨refl ⟩
  
    (Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ∘ᵥ associator.from {f = Coequalizer.obj (CoeqBimods B₄ B₃)} {F₂} {F₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ assoc₂ ⟩
  
    Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ (Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ∘ᵥ associator.from {f = Coequalizer.obj (CoeqBimods B₄ B₃)} {F₂} {F₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ refl⟩∘⟨ assoc₂ ⟩
  
    Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ∘ᵥ associator.from {f = Coequalizer.obj (CoeqBimods B₄ B₃)} {F₂} {F₁}
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-◁-∘₁ ⟩
  
    Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ (F₂ ∘₁ F₁)
    ∘ᵥ associator.from {f = F₄ ∘₁ F₃} {F₂} {F₁}
    ≈⟨ sym-assoc₂ ⟩
  
    (Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ (F₂ ∘₁ F₁)
    ∘ᵥ associator.from {f = F₄ ∘₁ F₃} {F₂} {F₁}
    ≈⟨ sym-assoc₂ ⟩
  
    ((Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ (F₂ ∘₁ F₁))
    ∘ᵥ associator.from {f = F₄ ∘₁ F₃} {F₂} {F₁}
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩
    
    (Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ (F₂ ∘₁ F₁))
    ∘ᵥ associator.from {f = F₄ ∘₁ F₃} {F₂} {F₁} ∎
    
    where
      open hom.HomReasoning

  face[43]21⇒4321 : Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
                    ∘ᵥ Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
                    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ (F₂ ∘₁ F₁)
                    ≈ (Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
                      ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
                      ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
                      ∘ᵥ associator.from {f = F₄} {F₃} {F₂ ∘₁ F₁}
  face[43]21⇒4321 = begin
  
    Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ (F₂ ∘₁ F₁)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ◁-▷-exchg ⟩

    Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ Coequalizer.obj (CoeqBimods B₂ B₁)
    ∘ᵥ (F₄ ∘₁ F₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ≈⟨ sym-assoc₂ ⟩

    (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁)))
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ Coequalizer.obj (CoeqBimods B₂ B₁)
    ∘ᵥ (F₄ ∘₁ F₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ≈⟨ sym-assoc₂ ⟩

    ((Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁)))
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ Coequalizer.obj (CoeqBimods B₂ B₁))
    ∘ᵥ (F₄ ∘₁ F₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ Coequalizer.obj (CoeqBimods B₂ B₁))
    ∘ᵥ (F₄ ∘₁ F₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ≈⟨ ⟺ (hexagon {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁}) ⟩∘⟨refl ⟩

    (Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ associator.from {f = F₄} {F₃} {Coequalizer.obj (CoeqBimods B₂ B₁)})
    ∘ᵥ (F₄ ∘₁ F₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ≈⟨ assoc₂ ⟩

    Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ associator.from {f = F₄} {F₃} {Coequalizer.obj (CoeqBimods B₂ B₁)})
    ∘ᵥ (F₄ ∘₁ F₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ≈⟨ refl⟩∘⟨ assoc₂ ⟩

    Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ associator.from {f = F₄} {F₃} {Coequalizer.obj (CoeqBimods B₂ B₁)}
    ∘ᵥ (F₄ ∘₁ F₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-▷-∘₁ ⟩

    Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂ ∘₁ F₁}
    ≈⟨ sym-assoc₂ ⟩

    (Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)))
    ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂ ∘₁ F₁}
    ≈⟨ sym-assoc₂ ⟩

    ((Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)))
    ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂ ∘₁ F₁}
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂ ∘₁ F₁} ∎
    
    where
      open hom.HomReasoning

  face[[43]2]1⇒[432]1 : Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁})
                        ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
                        ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
                        ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
                        ≈ (Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
                          ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁
                          ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁)
                          ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁
  face[[43]2]1⇒[432]1 = begin
  
    Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ sym-assoc₂ ⟩
  
    (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ ⟺ (αSq (Associator⊗From {B₃ = B₄} {B₃} {B₂}) (id-bimodule-hom {B = B₁})) ⟩∘⟨refl ⟩
  
    (Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂}) ◁ F₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ assoc₂ ⟩
  
    Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂}) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
  
    Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂}) ◁ F₁
    ∘ᵥ (Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂) ◁ F₁
    ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
  
    Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂})
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂) ◁ F₁
    ≈⟨ refl⟩∘⟨ ◁-resp-≈ (⟺ (hexagon {B₃ = B₄} {B₃} {B₂})) ⟩
  
    Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ (Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂}) ◁ F₁
    ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
  
    Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂}) ◁ F₁
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
  
    Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁
    ≈⟨ sym-assoc₂ ⟩
  
    (Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁)
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁
    ≈⟨ sym-assoc₂ ⟩
  
    ((Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁)
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁)
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁)
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁ ∎
    
    where
      open hom.HomReasoning

  face[432]1⇒4[32]1 : Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                      ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
                      ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁
                      ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁
                      ≈ (Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
                        ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                        ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁))
                        ∘ᵥ associator.from {f = F₄} {F₃ ∘₁ F₂} {F₁}
  face[432]1⇒4[32]1 = begin
  
    Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁
    ≈⟨ sym-assoc₂ ⟩
  
    (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁
    ≈⟨ sym-assoc₂ ⟩
  
    ((Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁)
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩
  
    (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁)
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁
    ≈⟨ ⟺ (hexagon {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁}) ⟩∘⟨refl ⟩
  
    (Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ associator.from {f = F₄} {Coequalizer.obj (CoeqBimods B₃ B₂)} {F₁})
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁
    ≈⟨ assoc₂ ⟩
  
    Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ associator.from {f = F₄} {Coequalizer.obj (CoeqBimods B₃ B₂)} {F₁})
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁
    ≈⟨ refl⟩∘⟨ assoc₂ ⟩
  
    Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ associator.from {f = F₄} {Coequalizer.obj (CoeqBimods B₃ B₂)} {F₁}
    ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-▷-◁ ⟩
  
    Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁)
    ∘ᵥ associator.from {f = F₄} {F₃ ∘₁ F₂} {F₁}
    ≈⟨ sym-assoc₂ ⟩
  
    (Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
    ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁)
    ∘ᵥ associator.from {f = F₄} {F₃ ∘₁ F₂} {F₁}
    ≈⟨ sym-assoc₂ ⟩
  
    ((Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
    ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁))
    ∘ᵥ associator.from {f = F₄} {F₃ ∘₁ F₂} {F₁}
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩
    
    (Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁))
    ∘ᵥ associator.from {f = F₄} {F₃ ∘₁ F₂} {F₁} ∎
    
    where
      open hom.HomReasoning

  face4[32]1⇒4321 : Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
                    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
                    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                    ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁)
                    ≈ (Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
                      ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
                      ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
                      ∘ᵥ F₄ ▷ associator.from {f = F₃} {F₂} {F₁}
  face4[32]1⇒4321 = begin

    Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁)
    ≈⟨ sym-assoc₂ ⟩

    (Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁)))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁)
    ≈⟨ ⟺ (αSq (id-bimodule-hom {B = B₄}) (Associator⊗From {B₃ = B₃} {B₂} {B₁})) ⟩∘⟨refl ⟩

    (Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Bimodhom.α (Associator⊗From {B₃ = B₃} {B₂} {B₁}))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁)
    ≈⟨ assoc₂ ⟩

    Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Bimodhom.α (Associator⊗From {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩

    Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Bimodhom.α (Associator⊗From {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
             ∘ᵥ Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁)
    ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩

    Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ (Bimodhom.α (Associator⊗From {B₃ = B₃} {B₂} {B₁})
             ∘ᵥ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
             ∘ᵥ Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁)
    ≈⟨ refl⟩∘⟨ ▷-resp-≈ (⟺ (hexagon {B₃ = B₃} {B₂} {B₁})) ⟩

    Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
             ∘ᵥ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
             ∘ᵥ associator.from {f = F₃} {F₂} {F₁})
    ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩

    Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ (F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
             ∘ᵥ associator.from {f = F₃} {F₂} {F₁})
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩

    Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ∘ᵥ F₄ ▷ associator.from {f = F₃} {F₂} {F₁}
    ≈⟨ sym-assoc₂ ⟩

    (Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)))
    ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
    ∘ᵥ F₄ ▷ associator.from {f = F₃} {F₂} {F₁}
    ≈⟨ sym-assoc₂ ⟩

    ((Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)))
    ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
    ∘ᵥ F₄ ▷ associator.from {f = F₃} {F₂} {F₁}
    ≈⟨ assoc₂ ⟩∘⟨refl ⟩

    (Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
    ∘ᵥ F₄ ▷ associator.from {f = F₃} {F₂} {F₁} ∎

    where
      open hom.HomReasoning

abstract
  pentagon⊗∘arr³ : (((Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
                   ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                   ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
                   ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                   ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁)
                   ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
                   ≈ (((Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                     ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
                     ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                     ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁)
                     ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
  pentagon⊗∘arr³ = begin
  
    (((Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ assoc₂ ⟩
  
    ((Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ assoc₂ ⟩
  
    (Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ assoc₂ ⟩
  
    Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ refl⟩∘⟨ assoc₂ ⟩
  
    Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
      ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁})
      ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
      ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
      ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ face[[43]2]1⇒[432]1 ⟩
  
    Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
      ∘ᵥ (Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
      ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁
      ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁)
      ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁
    ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩
  
    Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
      ∘ᵥ (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
      ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃ ⊗₀ B₂) B₁)
      ∘ᵥ Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂)) ◁ F₁
      ∘ᵥ (F₄ ▷ Coequalizer.arr (CoeqBimods B₃ B₂)) ◁ F₁)
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁
    ≈⟨ refl⟩∘⟨ face[432]1⇒4[32]1 ⟩∘⟨refl ⟩
  
    Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
      ∘ᵥ ((Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
      ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁))
      ∘ᵥ associator.from {f = F₄} {F₃ ∘₁ F₂} {F₁})
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁
    ≈⟨ refl⟩∘⟨ assoc₂ ⟩
  
    Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
      ∘ᵥ (Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
      ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁))
    ∘ᵥ associator.from {f = F₄} {F₃ ∘₁ F₂} {F₁}
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁
    ≈⟨ sym-assoc₂ ⟩
  
      (Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
      ∘ᵥ Coequalizer.arr (CoeqBimods B₄ ((B₃ ⊗₀ B₂) ⊗₀  B₁))
      ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ F₄ ▷ (Coequalizer.arr (CoeqBimods B₃ B₂) ◁ F₁))
    ∘ᵥ associator.from {f = F₄} {F₃ ∘₁ F₂} {F₁}
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁
    ≈⟨ face4[32]1⇒4321 ⟩∘⟨refl ⟩
  
      ((Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
      ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
      ∘ᵥ F₄ ▷ associator.from {f = F₃} {F₂} {F₁})
    ∘ᵥ associator.from {f = F₄} {F₃ ∘₁ F₂} {F₁}
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁
    ≈⟨ assoc₂ ⟩
  
      (Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
      ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
    ∘ᵥ F₄ ▷ associator.from {f = F₃} {F₂} {F₁}
    ∘ᵥ associator.from {f = F₄} {F₃ ∘₁ F₂} {F₁}
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂} ◁ F₁
    ≈⟨ refl⟩∘⟨ pentagon ⟩
  
      (Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
      ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
    ∘ᵥ associator.from {f = F₄} {F₃} {F₂ ∘₁ F₁}
    ∘ᵥ associator.from {f = F₄ ∘₁ F₃} {F₂} {F₁}
    ≈⟨ sym-assoc₂ ⟩
  
      ((Coequalizer.arr (CoeqBimods B₄ (B₃ ⊗₀ B₂ ⊗₀ B₁))
      ∘ᵥ F₄ ▷ Coequalizer.arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
      ∘ᵥ F₄ ▷ F₃ ▷ Coequalizer.arr (CoeqBimods B₂ B₁))
      ∘ᵥ associator.from {f = F₄} {F₃} {F₂ ∘₁ F₁})
    ∘ᵥ associator.from {f = F₄ ∘₁ F₃} {F₂} {F₁}
    ≈⟨ ⟺ face[43]21⇒4321 ⟩∘⟨refl ⟩
  
      (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
      ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
      ∘ᵥ Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
      ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ (F₂ ∘₁ F₁))
    ∘ᵥ associator.from {f = F₄ ∘₁ F₃} {F₂} {F₁}
    ≈⟨ assoc₂ ⟩
  
    Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
      ∘ᵥ (Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) (B₂ ⊗₀ B₁))
      ∘ᵥ Coequalizer.obj (CoeqBimods B₄ B₃) ▷ Coequalizer.arr (CoeqBimods B₂ B₁)
      ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ (F₂ ∘₁ F₁))
      ∘ᵥ associator.from {f = F₄ ∘₁ F₃} {F₂} {F₁}
    ≈⟨ refl⟩∘⟨ ⟺ face[[43]2]1⇒[43]21 ⟩
  
    Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
      ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
      ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
      ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
      ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ sym-assoc₂ ⟩
  
    (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ sym-assoc₂ ⟩
  
    ((Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁
    ≈⟨ sym-assoc₂ ⟩
      
    (((Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
    ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁)
    ∘ᵥ Coequalizer.arr (CoeqBimods B₄ B₃) ◁ F₂ ◁ F₁ ∎
      
    where
      open hom.HomReasoning

abstract
  pentagon⊗∘arr² : ((Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
                   ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                   ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
                   ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                   ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
                   ≈ ((Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                     ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
                     ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                     ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁
  pentagon⊗∘arr² = Coequalizer⇒Epi
  
                     ((CoeqBimods B₄ B₃) coeq-◁ F₂ coeq-◁ F₁)
                     
                     (((Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
                     ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                     ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
                     ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                     ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁)
                     
                     (((Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                     ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
                     ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                     ∘ᵥ Coequalizer.arr (CoeqBimods (B₄ ⊗₀ B₃) B₂) ◁ F₁)
                     
                     pentagon⊗∘arr³

  pentagon⊗∘arr : (Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
                  ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                  ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
                  ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
                   ≈ (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                     ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
                     ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
  pentagon⊗∘arr = Coequalizer⇒Epi
  
                    ((CoeqBimods (B₄ ⊗₀ B₃) B₂) coeq-◁ F₁)
                     
                    ((Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
                    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
                    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                  
                    ((Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                    ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
                    ∘ᵥ Coequalizer.arr (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁))
                    
                    pentagon⊗∘arr²

  pentagon⊗ : Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
              ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
              ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁})
              ≈ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁})
  pentagon⊗ = Coequalizer⇒Epi
  
                (CoeqBimods ((B₄ ⊗₀ B₃) ⊗₀ B₂) B₁)
                     
                (Bimodhom.α (id-bimodule-hom {B = B₄} ⊗₁ Associator⊗From {B₃ = B₃} {B₂} {B₁})
                ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃ ⊗₀ B₂} {B₁})
                ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂} ⊗₁ id-bimodule-hom {B = B₁}))
                  
                (Bimodhom.α (Associator⊗From {B₃ = B₄} {B₃} {B₂ ⊗₀ B₁})
                ∘ᵥ Bimodhom.α (Associator⊗From {B₃ = B₄ ⊗₀ B₃} {B₂} {B₁}))
                    
                pentagon⊗∘arr
