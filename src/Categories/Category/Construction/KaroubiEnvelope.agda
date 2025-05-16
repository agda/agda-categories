{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; _[_≈_])

-- Karoubi Envelopes. These are the free completions of categories under split idempotents
module Categories.Category.Construction.KaroubiEnvelope {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Morphism.Idempotent.Bundles 𝒞
open import Categories.Morphism.Reasoning 𝒞

private
  module 𝒞 = Category 𝒞
  open 𝒞.HomReasoning
  open 𝒞.Equiv

  open Idempotent
  open Idempotent⇒

KaroubiEnvelope : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
KaroubiEnvelope = record
  { Obj = Idempotent
  ; _⇒_ = Idempotent⇒
  ; _≈_ = λ f g → 𝒞 [ Idempotent⇒.hom f ≈ Idempotent⇒.hom g ]
  ; id = id
  ; _∘_ = _∘_
  ; assoc = 𝒞.assoc
  ; sym-assoc = 𝒞.sym-assoc
  ; identityˡ = λ {I} {J} {f} → absorbˡ f
  ; identityʳ = λ {I} {J} {f} → absorbʳ f
  ; identity² = λ {I} → idempotent I
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≈ = 𝒞.∘-resp-≈
  }
