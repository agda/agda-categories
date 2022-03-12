{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

module Categories.Morphism.Extremal.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (_$_)

open import Categories.Diagram.Equalizer 𝒞
open import Categories.Diagram.Coequalizer 𝒞

open import Categories.Morphism 𝒞
open import Categories.Morphism.Extremal 𝒞
open import Categories.Morphism.Properties 𝒞
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Morphism.Regular 𝒞

open Category 𝒞
open HomReasoning

--------------------------------------------------------------------------------
-- Extremal Epimorphisms

RegularEpi⇒IsExtremalEpi : ∀ {A B} {f : A ⇒ B} (e : RegularEpi f) → IsExtremalEpi (RegularEpi⇒Epi e)
RegularEpi⇒IsExtremalEpi {A = A} {B = B} {f = f} regular {X = X} {i = i} {g = k} i-mono f≈i∘k =
  record
    { inv = i⁻¹
    ; iso = record
      { isoˡ = isoˡ
      ; isoʳ = isoʳ
      }
    }
  where
    open RegularEpi regular
    open IsCoequalizer coequalizer

    i⁻¹ : B ⇒ X
    i⁻¹ = coequalize {h = k} $ i-mono (k ∘ h) (k ∘ g) $ begin
        i ∘ k ∘ h ≈⟨ pullˡ (⟺ f≈i∘k) ⟩
        f ∘ h     ≈⟨ equality ⟩
        f ∘ g     ≈⟨ pushˡ f≈i∘k ⟩
        i ∘ k ∘ g ∎

    isoʳ : i ∘ i⁻¹ ≈ id
    isoʳ = RegularEpi⇒Epi regular (i ∘ i⁻¹) id $ begin
      (i ∘ i⁻¹) ∘ f ≈⟨ pullʳ (⟺ universal) ⟩
      i ∘ k         ≈˘⟨ f≈i∘k ⟩
      f             ≈˘⟨ identityˡ ⟩
      id ∘ f        ∎

    isoˡ : i⁻¹ ∘ i ≈ id
    isoˡ = i-mono (i⁻¹ ∘ i) id $ begin
      i ∘ i⁻¹ ∘ i ≈⟨ cancelˡ isoʳ ⟩
      i           ≈˘⟨ identityʳ ⟩
      i ∘ id      ∎

private
  variable
    A B C D : Obj
    f g h i : A ⇒ B

RegularEpi⇒ExtremalEpi : (e : RegularEpi f) → ExtremalEpi f
RegularEpi⇒ExtremalEpi e = record
  { epi = RegularEpi⇒Epi e
  ; extremal = RegularEpi⇒IsExtremalEpi e
  }

ExtremalEpi-∘₂ : ExtremalEpi (f ∘ g) → ExtremalEpi f
ExtremalEpi-∘₂ fg-extremal = record
  { epi = Epi-∘₂ epi
  ; extremal = λ i-mono eq → extremal i-mono (pushˡ eq)
  }
  where
    open ExtremalEpi fg-extremal

ExtremalEpi+Mono⇒IsIso : ExtremalEpi f → Mono f → IsIso f
ExtremalEpi+Mono⇒IsIso {f = f} f-extremal f-mono = extremal f-mono (⟺ identityʳ)
  where
    open ExtremalEpi f-extremal


module _ (is-iso : ∀ {A B} {f : A ⇒ B} → Mono f → Epi f → IsIso f) where

  Mono+Epi⇒IsExtremalEpi : (e : Epi f) → IsExtremalEpi e
  Mono+Epi⇒IsExtremalEpi {f = f} f-epi {i = i} {g = g} i-mono f≈i∘g = is-iso i-mono i-epi
    where
      i-epi : Epi i
      i-epi g₁ g₂ g₁∘i≈g₂∘i = f-epi g₁ g₂ $ begin
        g₁ ∘ f       ≈⟨ pushʳ f≈i∘g ⟩
        (g₁ ∘ i) ∘ g ≈⟨ g₁∘i≈g₂∘i ⟩∘⟨refl ⟩
        (g₂ ∘ i) ∘ g ≈⟨ pullʳ (⟺ f≈i∘g) ⟩
        g₂ ∘ f ∎
