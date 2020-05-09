{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Morphism.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open import Data.Product using (_,_; _×_)

open Category 𝒞
open Definitions 𝒞
open HomReasoning

import Categories.Morphism as M
open M 𝒞
open import Categories.Morphism.Reasoning 𝒞

private
  variable
    A B C D : Obj
    f g h i : A ⇒ B

module _ (iso : Iso f g) where

  open Iso iso

  Iso-resp-≈ : f ≈ h → g ≈ i → Iso h i
  Iso-resp-≈ {h = h} {i = i} eq₁ eq₂ = record
    { isoˡ = begin
      i ∘ h ≈˘⟨ eq₂ ⟩∘⟨ eq₁ ⟩
      g ∘ f ≈⟨ isoˡ ⟩
      id    ∎
    ; isoʳ = begin
      h ∘ i ≈˘⟨ eq₁ ⟩∘⟨ eq₂ ⟩
      f ∘ g ≈⟨ isoʳ ⟩
      id    ∎
    }

  Iso-swap : Iso g f
  Iso-swap = record
    { isoˡ = isoʳ
    ; isoʳ = isoˡ
    }

  Iso⇒Mono : Mono f
  Iso⇒Mono h i eq = begin
    h           ≈⟨ introˡ isoˡ ⟩
    (g ∘ f) ∘ h ≈⟨ pullʳ eq ⟩
    g ∘ f ∘ i   ≈⟨ cancelˡ isoˡ ⟩
    i           ∎

  Iso⇒Epi : Epi f
  Iso⇒Epi h i eq = begin
    h           ≈⟨ introʳ isoʳ ⟩
    h ∘ f ∘ g   ≈⟨ pullˡ eq ⟩
    (i ∘ f) ∘ g ≈⟨ cancelʳ isoʳ ⟩
    i           ∎

Iso-∘ : Iso f g → Iso h i → Iso (h ∘ f) (g ∘ i)
Iso-∘ {f = f} {g = g} {h = h} {i = i} iso iso′ = record
  { isoˡ = begin
    (g ∘ i) ∘ h ∘ f ≈⟨ cancelInner (isoˡ iso′) ⟩
    g ∘ f           ≈⟨ isoˡ iso ⟩
    id              ∎
  ; isoʳ = begin
    (h ∘ f) ∘ g ∘ i ≈⟨ cancelInner (isoʳ iso) ⟩
    h ∘ i           ≈⟨ isoʳ iso′ ⟩
    id              ∎
  }
  where open Iso

Iso-≈ : f ≈ h → Iso f g → Iso h i → g ≈ i
Iso-≈ {f = f} {h = h} {g = g} {i = i} eq iso iso′ = begin
  g           ≈⟨ introˡ (isoˡ iso′) ⟩
  (i ∘ h) ∘ g ≈˘⟨ (refl⟩∘⟨ eq) ⟩∘⟨refl ⟩
  (i ∘ f) ∘ g ≈⟨ cancelʳ (isoʳ iso) ⟩
  i           ∎
  where open Iso

module _ where
  open _≅_

  isos×≈⇒≈ : ∀ {f g : A ⇒ B} → h ≈ i → (iso₁ : A ≅ C) → (iso₂ : B ≅ D) →
               CommutativeSquare f (from iso₁) (from iso₂) h →
               CommutativeSquare g (from iso₁) (from iso₂) i →
               f ≈ g
  isos×≈⇒≈ {h = h} {i = i} {f = f} {g = g} eq iso₁ iso₂ sq₁ sq₂ = begin
    f ≈⟨ switch-fromtoˡ iso₂ sq₁ ⟩
    to iso₂ ∘ h ∘ from iso₁ ≈⟨ refl⟩∘⟨ (eq ⟩∘⟨refl ) ⟩
    to iso₂ ∘ i ∘ from iso₁ ≈˘⟨ switch-fromtoˡ iso₂ sq₂ ⟩
    g ∎
