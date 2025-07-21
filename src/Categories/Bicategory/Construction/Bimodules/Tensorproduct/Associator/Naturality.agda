{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism
  renaming (Bimodulehomomorphism to Bimodhom)


-- We will define the associator in the bicategory of monads and bimodules. --

module Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator.Naturality
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} {M₁ M₂ M₃ M₄ : Monad 𝒞}
  {B₃ B₃' : Bimodule M₃ M₄} {B₂ B₂' : Bimodule M₂ M₃} {B₁ B₁' : Bimodule M₁ M₂}
  (f₃ : Bimodhom B₃ B₃') (f₂ : Bimodhom B₂ B₂') (f₁ : Bimodhom B₁ B₁') where

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

-- To get constructions of the hom-categories with implicit arguments into scope --
private
  module HomCat {X} {Y} where
    open Categories.Diagram.Coequalizer (hom X Y) public

open HomCat


open Bimodule B₁ using () renaming (F to F₁)
open Bimodule B₃ using () renaming (F to F₃)
open Bimodule B₁' using () renaming (F to F₁')
open Bimodule B₂' using () renaming (F to F₂')
open Bimodule B₃' using () renaming (F to F₃')

open TensorproductOfBimodules B₂ B₁ using (F₂⊗F₁)
open TensorproductOfBimodules B₃ B₂ using () renaming (F₂⊗F₁ to F₃⊗F₂)
open TensorproductOfBimodules B₃ (B₂ ⊗₀ B₁) using () renaming (F₂⊗F₁ to F₃⊗[F₂⊗F₁])
open TensorproductOfBimodules (B₃ ⊗₀ B₂) B₁ using () renaming (F₂⊗F₁ to [F₃⊗F₂]⊗F₁)

open TensorproductOfBimodules B₂' B₁' using () renaming (F₂⊗F₁ to F₂'⊗F₁')
open TensorproductOfBimodules B₃' B₂' using () renaming (F₂⊗F₁ to F₃'⊗F₂')
open TensorproductOfBimodules (B₃' ⊗₀ B₂') B₁' using () renaming (F₂⊗F₁ to [F₃'⊗F₂']⊗F₁')
open TensorproductOfBimodules B₃' (B₂' ⊗₀ B₁') using () renaming (F₂⊗F₁ to F₃'⊗[F₂'⊗F₁'])


open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator
  {o} {ℓ} {e} {t} {𝒞} {localCoeq} {M₁} {M₂} {M₃} {M₄}
  using (Associator⊗; α⇒⊗; hexagon)
  
abstract
  α⇒⊗-natural∘arr∘arr : ((α⇒⊗ {B₃'} {B₂'} {B₁'}
                          ∘ᵥ Bimodhom.α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                          ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
                          ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁
                        ≈ ((Bimodhom.α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
                            ∘ᵥ α⇒⊗ {B₃} {B₂} {B₁})
                            ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
                            ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁
  α⇒⊗-natural∘arr∘arr = begin

    ((α⇒⊗ {B₃'} {B₂'} {B₁'}
      ∘ᵥ Bimodhom.α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
      ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
      ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ≈⟨ assoc₂ ⟩

    (α⇒⊗ {B₃'} {B₂'} {B₁'}
      ∘ᵥ Bimodhom.α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
      ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
      ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ≈⟨ assoc₂ ⟩

    α⇒⊗ {B₃'} {B₂'} {B₁'}
    ∘ᵥ Bimodhom.α ((f₃ ⊗₁ f₂) ⊗₁ f₁)
    ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
    ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

    α⇒⊗
    ∘ᵥ (Bimodhom.α ((f₃ ⊗₁ f₂) ⊗₁ f₁)
    ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
    ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ≈⟨ refl⟩∘⟨ ⟺ αSq[f₃⊗f₂]⊗f₁ ⟩∘⟨refl ⟩

    α⇒⊗
    ∘ᵥ (Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ Bimodhom.α (f₃ ⊗₁ f₂) ⊚₁ Bimodhom.α f₁)
    ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩

    α⇒⊗
    ∘ᵥ Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ Bimodhom.α (f₃ ⊗₁ f₂) ⊚₁ Bimodhom.α f₁
    ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                     ⟺ identity₂ˡ ⟩⊚⟨ ⟺ identity₂ʳ
                                   ⟩∘⟨refl ⟩

    α⇒⊗
    ∘ᵥ Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ (id₂ ∘ᵥ Bimodhom.α (f₃ ⊗₁ f₂))
        ⊚₁ (Bimodhom.α f₁ ∘ᵥ id₂)
    ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                     ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩

    α⇒⊗
    ∘ᵥ Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ (Coequalizer.obj F₃'⊗F₂' ▷ Bimodhom.α f₁
    ∘ᵥ Bimodhom.α (f₃ ⊗₁ f₂) ◁ F₁)
    ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc₂ ⟩

    α⇒⊗
    ∘ᵥ Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ Coequalizer.obj F₃'⊗F₂' ▷ Bimodhom.α f₁
    ∘ᵥ Bimodhom.α (f₃ ⊗₁ f₂) ◁ F₁
    ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                                     ◁-resp-sq (⟺ αSqf₃⊗f₂) ⟩

    α⇒⊗
    ∘ᵥ Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ Coequalizer.obj F₃'⊗F₂' ▷ Bimodhom.α f₁
    ∘ᵥ Coequalizer.arr F₃'⊗F₂' ◁ F₁
    ∘ᵥ Bimodhom.α f₃ ⊚₁ Bimodhom.α f₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                              sym-assoc₂ ⟩

    α⇒⊗
    ∘ᵥ Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ (Coequalizer.obj F₃'⊗F₂' ▷ Bimodhom.α f₁
    ∘ᵥ Coequalizer.arr F₃'⊗F₂' ◁ F₁)
    ∘ᵥ Bimodhom.α f₃ ⊚₁ Bimodhom.α f₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                              ◁-▷-exchg ⟩∘⟨refl ⟩

    α⇒⊗
    ∘ᵥ Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ (Coequalizer.arr F₃'⊗F₂' ◁ F₁'
    ∘ᵥ (F₃' ∘₁ F₂') ▷ Bimodhom.α f₁)
    ∘ᵥ Bimodhom.α f₃ ⊚₁ Bimodhom.α f₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                                              assoc₂ ⟩

    α⇒⊗
    ∘ᵥ Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ Coequalizer.arr F₃'⊗F₂' ◁ F₁'
    ∘ᵥ (F₃' ∘₁ F₂') ▷ Bimodhom.α f₁
    ∘ᵥ Bimodhom.α f₃ ⊚₁ Bimodhom.α f₂ ◁ F₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                                              ⟺ ∘ᵥ-distr-⊚ ⟩

    α⇒⊗
    ∘ᵥ Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ Coequalizer.arr F₃'⊗F₂' ◁ F₁'
    ∘ᵥ (id₂ ∘ᵥ Bimodhom.α f₃ ⊚₁ Bimodhom.α f₂)
        ⊚₁ (Bimodhom.α f₁ ∘ᵥ id₂) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                                     identity₂ˡ ⟩⊚⟨ identity₂ʳ ⟩

    α⇒⊗
    ∘ᵥ Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ Coequalizer.arr F₃'⊗F₂' ◁ F₁'
    ∘ᵥ (Bimodhom.α f₃ ⊚₁ Bimodhom.α f₂)
        ⊚₁ Bimodhom.α f₁ ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

    α⇒⊗
    ∘ᵥ (Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ Coequalizer.arr F₃'⊗F₂' ◁ F₁')
    ∘ᵥ (Bimodhom.α f₃ ⊚₁ Bimodhom.α f₂)
        ⊚₁ Bimodhom.α f₁ ≈⟨ sym-assoc₂ ⟩

    (α⇒⊗
    ∘ᵥ Coequalizer.arr [F₃'⊗F₂']⊗F₁'
    ∘ᵥ Coequalizer.arr F₃'⊗F₂' ◁ F₁')
    ∘ᵥ (Bimodhom.α f₃ ⊚₁ Bimodhom.α f₂)
        ⊚₁ Bimodhom.α f₁ ≈⟨ ⟺ (hexagon {B₃'} {B₂'} {B₁'}) ⟩∘⟨refl ⟩

    (Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ F₃' ▷ Coequalizer.arr F₂'⊗F₁'
    ∘ᵥ associator.from)
    ∘ᵥ (Bimodhom.α f₃ ⊚₁ Bimodhom.α f₂)
        ⊚₁ Bimodhom.α f₁ ≈⟨ assoc₂ ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ (F₃' ▷ Coequalizer.arr F₂'⊗F₁'
    ∘ᵥ associator.from)
    ∘ᵥ (Bimodhom.α f₃ ⊚₁ Bimodhom.α f₂)
        ⊚₁ Bimodhom.α f₁ ≈⟨ refl⟩∘⟨ assoc₂ ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ F₃' ▷ Coequalizer.arr F₂'⊗F₁'
    ∘ᵥ associator.from
    ∘ᵥ (Bimodhom.α f₃ ⊚₁ Bimodhom.α f₂)
        ⊚₁ Bimodhom.α f₁ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-⊚ ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ F₃' ▷ Coequalizer.arr F₂'⊗F₁'
    ∘ᵥ Bimodhom.α f₃
       ⊚₁ (Bimodhom.α f₂ ⊚₁ Bimodhom.α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                          (⟺ identity₂ʳ) ⟩⊚⟨ (⟺ identity₂ˡ)
                        ⟩∘⟨refl ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ F₃' ▷ Coequalizer.arr F₂'⊗F₁'
    ∘ᵥ (Bimodhom.α f₃ ∘ᵥ id₂)
       ⊚₁ (id₂ ∘ᵥ Bimodhom.α f₂ ⊚₁ Bimodhom.α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                          ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ F₃' ▷ Coequalizer.arr F₂'⊗F₁'
    ∘ᵥ (Bimodhom.α f₃ ◁ (F₂' ∘₁ F₁')
    ∘ᵥ F₃ ▷ Bimodhom.α f₂ ⊚₁ Bimodhom.α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ (F₃' ▷ Coequalizer.arr F₂'⊗F₁'
    ∘ᵥ Bimodhom.α f₃ ◁ (F₂' ∘₁ F₁')
    ∘ᵥ F₃ ▷ Bimodhom.α f₂ ⊚₁ Bimodhom.α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩∘⟨refl ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ ((F₃' ▷ Coequalizer.arr F₂'⊗F₁'
    ∘ᵥ Bimodhom.α f₃ ◁ (F₂' ∘₁ F₁'))
    ∘ᵥ F₃ ▷ Bimodhom.α f₂ ⊚₁ Bimodhom.α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ (◁-▷-exchg ⟩∘⟨refl) ⟩∘⟨refl ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ ((Bimodhom.α f₃ ◁ Coequalizer.obj F₂'⊗F₁'
    ∘ᵥ F₃ ▷ Coequalizer.arr F₂'⊗F₁')
    ∘ᵥ F₃ ▷ Bimodhom.α f₂ ⊚₁ Bimodhom.α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ assoc₂ ⟩∘⟨refl ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ (Bimodhom.α f₃ ◁ Coequalizer.obj F₂'⊗F₁'
    ∘ᵥ F₃ ▷ Coequalizer.arr F₂'⊗F₁'
    ∘ᵥ F₃ ▷ Bimodhom.α f₂ ⊚₁ Bimodhom.α f₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ (refl⟩∘⟨
                          ▷-resp-sq αSqf₂⊗f₁) ⟩∘⟨refl ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ (Bimodhom.α f₃ ◁ Coequalizer.obj F₂'⊗F₁'
    ∘ᵥ F₃ ▷ Bimodhom.α (f₂ ⊗₁ f₁)
    ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ sym-assoc₂ ⟩∘⟨refl ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ ((Bimodhom.α f₃ ◁ Coequalizer.obj F₂'⊗F₁'
    ∘ᵥ F₃ ▷ Bimodhom.α (f₂ ⊗₁ f₁))
    ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ (⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl) ⟩∘⟨refl ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ ((Bimodhom.α f₃ ∘ᵥ id₂)
        ⊚₁ (id₂ ∘ᵥ Bimodhom.α (f₂ ⊗₁ f₁))
    ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁)
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ (identity₂ʳ ⟩⊚⟨ identity₂ˡ ⟩∘⟨refl) ⟩∘⟨refl ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ (Bimodhom.α f₃ ⊚₁ Bimodhom.α (f₂ ⊗₁ f₁)
    ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁)
    ∘ᵥ associator.from ≈⟨ (refl⟩∘⟨ assoc₂) ⟩

    Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ Bimodhom.α f₃ ⊚₁ Bimodhom.α (f₂ ⊗₁ f₁)
    ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
    ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩

    (Coequalizer.arr F₃'⊗[F₂'⊗F₁']
    ∘ᵥ Bimodhom.α f₃ ⊚₁ Bimodhom.α (f₂ ⊗₁ f₁))
    ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
    ∘ᵥ associator.from ≈⟨ αSqf₃⊗[f₂⊗f₁] ⟩∘⟨refl ⟩

    (Bimodhom.α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ Coequalizer.arr F₃⊗[F₂⊗F₁])
    ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
    ∘ᵥ associator.from ≈⟨ assoc₂ ⟩

    Bimodhom.α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ Coequalizer.arr F₃⊗[F₂⊗F₁]
    ∘ᵥ F₃ ▷ Coequalizer.arr F₂⊗F₁
    ∘ᵥ associator.from ≈⟨ refl⟩∘⟨ hexagon {B₃} {B₂} {B₁} ⟩

    Bimodhom.α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ α⇒⊗ {B₃} {B₂} {B₁}
    ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
    ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ≈⟨ sym-assoc₂ ⟩

    (Bimodhom.α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ α⇒⊗ {B₃} {B₂} {B₁})
    ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
    ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ≈⟨ sym-assoc₂ ⟩

    ((Bimodhom.α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
    ∘ᵥ α⇒⊗ {B₃} {B₂} {B₁})
    ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
    ∘ᵥ Coequalizer.arr F₃⊗F₂ ◁ F₁ ∎

    where
      open hom.HomReasoning
      open TensorproductOfHomomorphisms f₂ f₁ renaming (αSq to αSqf₂⊗f₁)
      open TensorproductOfHomomorphisms f₃ f₂ renaming (αSq to αSqf₃⊗f₂)
      open TensorproductOfHomomorphisms (f₃ ⊗₁ f₂) f₁ renaming (αSq to αSq[f₃⊗f₂]⊗f₁)
      open TensorproductOfHomomorphisms f₃ (f₂ ⊗₁ f₁) renaming (αSq to αSqf₃⊗[f₂⊗f₁])

  α⇒⊗-natural∘arr : (α⇒⊗ {B₃'} {B₂'} {B₁'}
                     ∘ᵥ Bimodhom.α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                     ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
                     ≈ (Bimodhom.α (f₃ ⊗₁ (f₂ ⊗₁ f₁)) ∘ᵥ α⇒⊗ {B₃} {B₂} {B₁})
                        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁
  α⇒⊗-natural∘arr = Coequalizer⇒Epi
                      (F₃⊗F₂ coeq-◁ F₁)
                      ((α⇒⊗ {B₃'} {B₂'} {B₁'}
                        ∘ᵥ Bimodhom.α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
                      ((Bimodhom.α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
                        ∘ᵥ α⇒⊗ {B₃} {B₂} {B₁})
                        ∘ᵥ Coequalizer.arr [F₃⊗F₂]⊗F₁)
                      α⇒⊗-natural∘arr∘arr

  α⇒⊗-natural : α⇒⊗ {B₃'} {B₂'} {B₁'}
                ∘ᵥ Bimodhom.α ((f₃ ⊗₁ f₂) ⊗₁ f₁)
                ≈ Bimodhom.α (f₃ ⊗₁ (f₂ ⊗₁ f₁))
                  ∘ᵥ α⇒⊗ {B₃} {B₂} {B₁}
  α⇒⊗-natural = Coequalizer⇒Epi
                      [F₃⊗F₂]⊗F₁
                      (α⇒⊗ ∘ᵥ Bimodhom.α ((f₃ ⊗₁ f₂) ⊗₁ f₁))
                      (Bimodhom.α (f₃ ⊗₁ f₂ ⊗₁ f₁) ∘ᵥ α⇒⊗)
                      α⇒⊗-natural∘arr
-- end abstract --
