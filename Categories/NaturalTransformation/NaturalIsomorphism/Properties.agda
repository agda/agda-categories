{-# OPTIONS --without-K --safe #-}

module Categories.NaturalTransformation.NaturalIsomorphism.Properties where

open import Level

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation.NaturalIsomorphism

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

private
  variable 
    o ℓ e : Level
    C D : Category o ℓ e


-- properties of natural isomorphisms over an endofunctor
module _ {F : Endofunctor C} where
  private
    module C = Category C
    module F = Functor F
    module MC = Mor C

  module _ (α : F ≃ idF) where
    open C
    open HomReasoning
    open F
    open MC
    open MR C
    open NaturalIsomorphism α
    
    F≃id-comm₁ : ∀ {A} → ⇒.η (F₀ A) ≈ F₁ (⇒.η A)
    F≃id-comm₁ {A} = begin
      ⇒.η (F₀ A)                           ≈⟨ introʳ (F-resp-≈ (iso.isoˡ _) ○ identity) ⟩
      ⇒.η (F₀ A) ∘ F₁ (⇐.η A ∘ ⇒.η A)      ≈⟨ refl⟩∘⟨ homomorphism ⟩
      ⇒.η (F₀ A) ∘ F₁ (⇐.η A) ∘ F₁ (⇒.η A) ≈⟨ cancelˡ (⇒.commute _ ○ iso.isoˡ _) ⟩
      F₁ (⇒.η A)                           ∎

    F≃id-comm₂ : ∀ {A} → ⇐.η (F₀ A) ≈ F₁ (⇐.η A)
    F≃id-comm₂ {A} = begin
      ⇐.η (F₀ A)                             ≈⟨ introˡ (F-resp-≈ (iso.isoˡ _) ○ identity) ⟩
      F₁ (⇐.η A ∘ ⇒.η A) ∘ ⇐.η (F₀ A)        ≈⟨ homomorphism ⟩∘⟨refl ⟩
      (F₁ (⇐.η A) ∘ F₁ (⇒.η A)) ∘ ⇐.η (F₀ A) ≈⟨ cancelʳ (⟺ (⇐.commute _) ○ iso.isoˡ _) ⟩
      F₁ (⇐.η A)                             ∎
