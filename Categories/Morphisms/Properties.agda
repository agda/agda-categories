{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Morphisms.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning

open import Categories.Morphisms 𝒞

private
  variable
    A B C : Obj
    f g h i : A ⇒ B

Iso-resp-≈ : Iso f g → f ≈ h → g ≈ i → Iso h i
Iso-resp-≈ {f = f} {g = g} {h = h} {i = i} iso eq₁ eq₂ = record
  { isoˡ = begin
    i ∘ h ≈⟨ sym eq₂ ⟩∘⟨ sym eq₁ ⟩
    g ∘ f ≈⟨ isoˡ ⟩
    id    ∎
  ; isoʳ = begin
    h ∘ i ≈⟨ sym eq₁ ⟩∘⟨ sym eq₂ ⟩
    f ∘ g ≈⟨ isoʳ ⟩
    id    ∎
  }
  where open Iso iso
