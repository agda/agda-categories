{-# OPTIONS --without-K --safe #-}



module Categories.Object.Zero.Properties where

open import Categories.Category
open import Categories.Object.Zero

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

module _ {o ℓ e} {𝒞 : Category o ℓ e} (∅ : Zero 𝒞) where
  open Category 𝒞
  open HomReasoning
  open Mor 𝒞
  open MR 𝒞
  open Zero ∅

  zero-mono-factor : ∀ {X Y Z} → (f : Y ⇒ Z) → (g : X ⇒ Y) → Mono f → f ∘ g ≈ zero⇒ → g ≈ zero⇒
  zero-mono-factor f g f-mono eq = f-mono g zero⇒ (eq ○ ⟺ (zero-∘ˡ f))
