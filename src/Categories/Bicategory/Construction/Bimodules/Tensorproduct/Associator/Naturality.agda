{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism


-- We will define the associator in the bicategory of monads and bimodules. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator.Naturality
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ M₄ : Monad 𝒞}
  {B₃ B₃' : Bimodule M₃ M₄} {B₂ B₂' : Bimodule M₂ M₃} {B₁ B₁' : Bimodule M₁ M₂}
  (f₃ : Bimodulehomomorphism B₃ B₃') (f₂ : Bimodulehomomorphism B₂ B₂') (f₁ : Bimodulehomomorphism B₁ B₁') where
  --- TODO: Rename B₁' → B'₁ etc. ---

import Categories.Bicategory.LocalCoequalizers
open ComposeWithLocalCoequalizer 𝒞 localCoeq

import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} as TensorproductOfBimodules
import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms {𝒞 = 𝒞} {localCoeq} as TensorproductOfHomomorphisms
open TensorproductOfBimodules using () renaming (Tensorproduct to infixr 30 _⊗₀_)
open TensorproductOfHomomorphisms using () renaming (Tensorproduct to infixr 30 _⊗₁_)

import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
import Categories.Diagram.Coequalizer

-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    open Categories.Diagram.Coequalizer (hom X Y) public
    open Coequalizer using (arr) public

open HomCat

open TensorproductOfBimodules using (CoeqBimods)

open Bimodule B₁ using () renaming (F to F₁)
open Bimodule B₃ using () renaming (F to F₃)
open Bimodule B₁' using () renaming (F to F₁')
open Bimodule B₂' using () renaming (F to F₂')
open Bimodule B₃' using () renaming (F to F₃')
open Bimodulehomomorphism using (α)

open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator
  {o} {ℓ} {e} {t} {𝒞} {localCoeq} {M₁} {M₂} {M₃} {M₄}
  using (α⇒-⊗; hexagon)
  
abstract
  α⇒-⊗-natural-∘arr² : ((α⇒-⊗ {B₃'} {B₂'} {B₁'}
                          ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                          ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                          ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁
                        ≈ ((α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
                            ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁})
                            ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                            ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁
  α⇒-⊗-natural-∘arr² = begin

    ((α⇒-⊗ {B₃'} {B₂'} {B₁'}
      ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
      ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ≈⟨ assoc₂ ⟩

    (α⇒-⊗ {B₃'} {B₂'} {B₁'}
      ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
      ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
      ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ≈⟨ assoc₂ ⟩

    α⇒-⊗ {B₃'} {B₂'} {B₁'}
    ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁)
    ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

    α⇒-⊗
    ∘ᵥ (α ((f₃ ⊗₁ f₂) ⊗₁ f₁)
    ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ≈⟨ refl⟩∘⟨ ⟺ (αSq-⊗ (f₃ ⊗₁ f₂) f₁) ⟩∘⟨refl ⟩

    α⇒-⊗
    ∘ᵥ (arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ α (f₃ ⊗₁ f₂) ⊚₁ α f₁)
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩

    α⇒-⊗
    ∘ᵥ arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ α (f₃ ⊗₁ f₂) ⊚₁ α f₁
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                     ⟺ identity₂ˡ ⟩⊚⟨ ⟺ identity₂ʳ
                                   ⟩∘⟨refl ⟩

    α⇒-⊗
    ∘ᵥ arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ (id₂ ∘ᵥ α (f₃ ⊗₁ f₂))
        ⊚₁ (α f₁ ∘ᵥ id₂)
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                     ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩

    α⇒-⊗
    ∘ᵥ arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ (Coequalizer.obj (CoeqBimods B₃' B₂') ▷ α f₁
    ∘ᵥ α (f₃ ⊗₁ f₂) ◁ F₁)
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

    α⇒-⊗
    ∘ᵥ arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ Coequalizer.obj (CoeqBimods B₃' B₂') ▷ α f₁
    ∘ᵥ α (f₃ ⊗₁ f₂) ◁ F₁
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                                     ◁-resp-sq (⟺ (αSq-⊗ f₃ f₂)) ⟩

    α⇒-⊗
    ∘ᵥ arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ Coequalizer.obj (CoeqBimods B₃' B₂') ▷ α f₁
    ∘ᵥ arr (CoeqBimods B₃' B₂') ◁ F₁
    ∘ᵥ α f₃ ⊚₁ α f₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                              sym-assoc₂ ⟩

    α⇒-⊗
    ∘ᵥ arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ (Coequalizer.obj (CoeqBimods B₃' B₂') ▷ α f₁
    ∘ᵥ arr (CoeqBimods B₃' B₂') ◁ F₁)
    ∘ᵥ α f₃ ⊚₁ α f₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                              ◁-▷-exchg ⟩∘⟨refl ⟩

    α⇒-⊗
    ∘ᵥ arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ (arr (CoeqBimods B₃' B₂') ◁ F₁'
    ∘ᵥ (F₃' ∘₁ F₂') ▷ α f₁)
    ∘ᵥ α f₃ ⊚₁ α f₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                              assoc₂ ⟩

    α⇒-⊗
    ∘ᵥ arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ arr (CoeqBimods B₃' B₂') ◁ F₁'
    ∘ᵥ (F₃' ∘₁ F₂') ▷ α f₁
    ∘ᵥ α f₃ ⊚₁ α f₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                                              ⟺ ∘ᵥ-distr-⊚ ⟩

    α⇒-⊗
    ∘ᵥ arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ arr (CoeqBimods B₃' B₂') ◁ F₁'
    ∘ᵥ (id₂ ∘ᵥ α f₃ ⊚₁ α f₂)
        ⊚₁ (α f₁ ∘ᵥ id₂) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                                     identity₂ˡ ⟩⊚⟨ identity₂ʳ ⟩

    α⇒-⊗
    ∘ᵥ arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ arr (CoeqBimods B₃' B₂') ◁ F₁'
    ∘ᵥ (α f₃ ⊚₁ α f₂)
        ⊚₁ α f₁ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

    α⇒-⊗
    ∘ᵥ (arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ arr (CoeqBimods B₃' B₂') ◁ F₁')
    ∘ᵥ (α f₃ ⊚₁ α f₂)
        ⊚₁ α f₁ ≈⟨ sym-assoc₂ ⟩

    (α⇒-⊗
    ∘ᵥ arr (CoeqBimods (B₃' ⊗₀ B₂') B₁')
    ∘ᵥ arr (CoeqBimods B₃' B₂') ◁ F₁')
    ∘ᵥ (α f₃ ⊚₁ α f₂)
        ⊚₁ α f₁ ≈⟨ ⟺ (hexagon {B₃'} {B₂'} {B₁'}) ⟩∘⟨refl ⟩

    (arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ F₃' ▷ arr (CoeqBimods B₂' B₁')
    ∘ᵥ associator.from)
    ∘ᵥ (α f₃ ⊚₁ α f₂)
        ⊚₁ α f₁ ≈⟨ assoc₂ ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ (F₃' ▷ arr (CoeqBimods B₂' B₁')
    ∘ᵥ associator.from)
    ∘ᵥ (α f₃ ⊚₁ α f₂)
        ⊚₁ α f₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ F₃' ▷ arr (CoeqBimods B₂' B₁')
    ∘ᵥ associator.from
    ∘ᵥ (α f₃ ⊚₁ α f₂)
        ⊚₁ α f₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-⊚ ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ F₃' ▷ arr (CoeqBimods B₂' B₁')
    ∘ᵥ α f₃
       ⊚₁ (α f₂ ⊚₁ α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                          (⟺ identity₂ʳ) ⟩⊚⟨ (⟺ identity₂ˡ)
                        ⟩∘⟨refl ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ F₃' ▷ arr (CoeqBimods B₂' B₁')
    ∘ᵥ (α f₃ ∘ᵥ id₂)
       ⊚₁ (id₂ ∘ᵥ α f₂ ⊚₁ α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                          ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ F₃' ▷ arr (CoeqBimods B₂' B₁')
    ∘ᵥ (α f₃ ◁ (F₂' ∘₁ F₁')
    ∘ᵥ F₃ ▷ α f₂ ⊚₁ α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ (F₃' ▷ arr (CoeqBimods B₂' B₁')
    ∘ᵥ α f₃ ◁ (F₂' ∘₁ F₁')
    ∘ᵥ F₃ ▷ α f₂ ⊚₁ α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩∘⟨refl ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ ((F₃' ▷ arr (CoeqBimods B₂' B₁')
    ∘ᵥ α f₃ ◁ (F₂' ∘₁ F₁'))
    ∘ᵥ F₃ ▷ α f₂ ⊚₁ α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ (◁-▷-exchg ⟩∘⟨refl) ⟩∘⟨refl ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ ((α f₃ ◁ Coequalizer.obj (CoeqBimods B₂' B₁')
    ∘ᵥ F₃ ▷ arr (CoeqBimods B₂' B₁'))
    ∘ᵥ F₃ ▷ α f₂ ⊚₁ α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ assoc₂ ⟩∘⟨refl ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ (α f₃ ◁ Coequalizer.obj (CoeqBimods B₂' B₁')
    ∘ᵥ F₃ ▷ arr (CoeqBimods B₂' B₁')
    ∘ᵥ F₃ ▷ α f₂ ⊚₁ α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ (refl⟩∘⟨
                          ▷-resp-sq (αSq-⊗ f₂ f₁)) ⟩∘⟨refl ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ (α f₃ ◁ Coequalizer.obj (CoeqBimods B₂' B₁')
    ∘ᵥ F₃ ▷ α (f₂ ⊗₁ f₁)
    ∘ᵥ F₃ ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩∘⟨refl ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ ((α f₃ ◁ Coequalizer.obj (CoeqBimods B₂' B₁')
    ∘ᵥ F₃ ▷ α (f₂ ⊗₁ f₁))
    ∘ᵥ F₃ ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ (⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl) ⟩∘⟨refl ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ ((α f₃ ∘ᵥ id₂)
        ⊚₁ (id₂ ∘ᵥ α (f₂ ⊗₁ f₁))
    ∘ᵥ F₃ ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ (identity₂ʳ ⟩⊚⟨ identity₂ˡ ⟩∘⟨refl) ⟩∘⟨refl ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ (α f₃ ⊚₁ α (f₂ ⊗₁ f₁)
    ∘ᵥ F₃ ▷ arr (CoeqBimods B₂ B₁))
    ∘ᵥ associator.from ≈⟨ (refl⟩∘⟨ assoc₂) ⟩

    arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ α f₃ ⊚₁ α (f₂ ⊗₁ f₁)
    ∘ᵥ F₃ ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩

    (arr (CoeqBimods B₃' (B₂' ⊗₀ B₁'))
    ∘ᵥ α f₃ ⊚₁ α (f₂ ⊗₁ f₁))
    ∘ᵥ F₃ ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ associator.from ≈⟨ αSq-⊗ f₃ (f₂ ⊗₁ f₁) ⟩∘⟨refl ⟩

    (α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁)))
    ∘ᵥ F₃ ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ associator.from ≈⟨ assoc₂ ⟩

    α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ arr (CoeqBimods B₃ (B₂ ⊗₀ B₁))
    ∘ᵥ F₃ ▷ arr (CoeqBimods B₂ B₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ hexagon {B₃} {B₂} {B₁} ⟩

    α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁}
    ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ≈⟨ sym-assoc₂ ⟩

    (α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁})
    ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ≈⟨ sym-assoc₂ ⟩

    ((α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁})
    ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
    ∘ᵥ arr (CoeqBimods B₃ B₂) ◁ F₁ ∎

    where
      open hom.HomReasoning
      open TensorproductOfHomomorphisms using (αSq-⊗)

  α⇒-⊗-natural-∘arr : (α⇒-⊗ {B₃'} {B₂'} {B₁'}
                     ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                     ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                     ≈ (α (f₃ ⊗₁ (f₂ ⊗₁ f₁)) ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁})
                        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁)
  α⇒-⊗-natural-∘arr = Coequalizer⇒Epi
                      ((CoeqBimods B₃ B₂) coeq-◁ F₁)
                      ((α⇒-⊗ {B₃'} {B₂'} {B₁'}
                        ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                      ((α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
                        ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁})
                        ∘ᵥ arr (CoeqBimods (B₃ ⊗₀ B₂) B₁))
                      α⇒-⊗-natural-∘arr²

  α⇒-⊗-natural : α⇒-⊗ {B₃'} {B₂'} {B₁'}
                ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁)
                ≈ α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
                  ∘ᵥ α⇒-⊗ {B₃} {B₂} {B₁}
  α⇒-⊗-natural = Coequalizer⇒Epi
                      (CoeqBimods (B₃ ⊗₀ B₂) B₁)
                      (α⇒-⊗ ∘ᵥ α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                      (α (f₃ ⊗₁ f₂ ⊗₁ f₁) ∘ᵥ α⇒-⊗)
                      α⇒-⊗-natural-∘arr
-- end abstract --
