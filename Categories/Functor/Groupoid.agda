{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Groupoid where

open import Level

open import Categories.Category
open import Categories.Category.IsGroupoid
open import Categories.Functor
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

-- functor respects groupoid inverse
module _ (GC : IsGroupoid C) (GD : IsGroupoid D) (F : Functor C D) where
  private
    module C = IsGroupoid GC
    module D = IsGroupoid GD
    open Functor F
    open D
    open HomReasoning
    open MR D
    
  F-resp-inv : ∀ {A B} (f : A C.⇒ B) → F₁ (f C.⁻¹) ≈ (F₁ f) ⁻¹
  F-resp-inv f = begin
    F₁ (f C.⁻¹)                      ≈⟨ introˡ D.iso.isoˡ ⟩
    ((F₁ f) ⁻¹ ∘ F₁ f) ∘ F₁ (f C.⁻¹) ≈˘⟨ pushʳ homomorphism ⟩
    (F₁ f) ⁻¹ ∘ F₁ (f C.∘ f C.⁻¹)    ≈⟨ elimʳ (F-resp-≈ C.iso.isoʳ ○ identity) ⟩
    (F₁ f) ⁻¹                        ∎
