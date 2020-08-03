{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Equalizer.Properties {o ℓ e} (C : Category o ℓ e) where

open import Categories.Diagram.Equalizer C
open import Categories.Morphism C
open import Categories.Morphism.Reasoning C

private
  module C = Category C
  open C

  variable
    X Y Z : Obj

module _ {f g : X ⇒ Y} (equalizer : Equalizer f g) where
  open Equalizer equalizer
  open HomReasoning

  equalizer-≈⇒≈ : ∀ {h} → arr ∘ h ≈ id → f ≈ g
  equalizer-≈⇒≈ {h} eq = begin
    f             ≈⟨ introʳ eq ⟩
    f ∘ arr ∘ h   ≈⟨ pullˡ equality ⟩
    (g ∘ arr) ∘ h ≈⟨ cancelʳ eq ⟩
    g             ∎
