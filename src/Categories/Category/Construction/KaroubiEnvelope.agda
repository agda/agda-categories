{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

-- Karoubi Envelopes. These are the free completions of categories under split idempotents
module Categories.Category.Construction.KaroubiEnvelope {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Morphism.Idempotent.Bundles 𝒞
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning
open Equiv

open BundledIdempotent
open Idempotent⇒

KaroubiEnvelope : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
KaroubiEnvelope = record
  { Obj = BundledIdempotent
  ; _⇒_ = Idempotent⇒
  ; _≈_ = λ f g → Idempotent⇒.hom f ≈ Idempotent⇒.hom g
  ; id = idempotent⇒-id
  ; _∘_ = idempotent⇒-∘
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = λ {I} {J} {f} → absorbˡ f
  ; identityʳ = λ {I} {J} {f} → absorbʳ f
  ; identity² = λ {I} → idempotent I
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≈ = ∘-resp-≈
  }
