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
    f g : X ⇒ Y

module _ (equalizer : Equalizer f g) where
  open Equalizer equalizer
  open HomReasoning

  equalizer-≈⇒≈ : ∀ {h} → arr ∘ h ≈ id → f ≈ g
  equalizer-≈⇒≈ {h} eq = begin
    f             ≈⟨ introʳ eq ⟩
    f ∘ arr ∘ h   ≈⟨ pullˡ equality ⟩
    (g ∘ arr) ∘ h ≈⟨ cancelʳ eq ⟩
    g             ∎

section-equalizer : ∀ {X Y} {f : Y ⇒ X} {g : X ⇒ Y} → f SectionOf g → IsEqualizer f (f ∘ g) id
section-equalizer {X = X} {Y = Y} {f = f} {g = g} g∘f≈id = record
  { equality = equality
  ; equalize = equalize
  ; universal = λ {_} {_} {eq} → universal {eq = eq}
  ; unique = unique
  }
  where
    open HomReasoning

    equality : (f ∘ g) ∘ f ≈ id ∘ f
    equality = begin
      (f ∘ g) ∘ f ≈⟨ pullʳ g∘f≈id ⟩
      f ∘ id      ≈⟨ id-comm ⟩
      id ∘ f      ∎

    equalize : ∀ {Z} {h : Z ⇒ X} → (f ∘ g) ∘ h ≈ id ∘ h → Z ⇒ Y
    equalize {h = h} _ = g ∘ h

    universal : ∀ {Z} {h : Z ⇒ X} {eq : (f ∘ g) ∘ h ≈ id ∘ h} → h ≈ f ∘ g ∘ h
    universal {h = h} {eq = eq} = begin
      h           ≈˘⟨ identityˡ ⟩
      id ∘ h      ≈˘⟨ eq ⟩
      (f ∘ g) ∘ h ≈⟨ assoc ⟩
      f ∘ g ∘ h   ∎

    unique : ∀ {Z} {h : Z ⇒ X} {i : Z ⇒ Y} → h ≈ f ∘ i → i ≈ g ∘ h
    unique {h = h} {i = i} h≈g∘i = begin
      i           ≈⟨ introˡ g∘f≈id ⟩
      (g ∘ f) ∘ i ≈⟨ pullʳ (⟺ h≈g∘i) ⟩
      g ∘ h       ∎
