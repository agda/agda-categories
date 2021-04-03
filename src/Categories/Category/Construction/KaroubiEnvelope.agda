{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

-- Karoubi Envelopes. These are the free completions of categories under split idempotents
module Categories.Category.Construction.KaroubiEnvelope {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Morphism.Idempotent 𝒞
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning
open Equiv

-- It's nicer to work with the bundled form of idempotents here.
-- We could use Σ types, but that gets a bit messy.
record BundledIdempotent : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj} : Obj
    isIdempotent : Idempotent obj

  open Idempotent isIdempotent public

record Idempotent⇒ (I J : BundledIdempotent) : Set (ℓ ⊔ e) where
  private
    module I = BundledIdempotent I
    module J = BundledIdempotent J
  field
    hom : I.obj ⇒ J.obj
    absorbˡ : J.idem ∘ hom ≈ hom
    absorbʳ : hom ∘ I.idem ≈ hom

open BundledIdempotent
open Idempotent⇒

KaroubiEnvelope : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
KaroubiEnvelope = record
  { Obj = BundledIdempotent
  ; _⇒_ = Idempotent⇒
  ; _≈_ = λ f g → Idempotent⇒.hom f ≈ Idempotent⇒.hom g
  ; id = λ {I} → record
    { hom = idem I
    ; absorbˡ = idempotent I
    ; absorbʳ = idempotent I
    }
  ; _∘_ = λ {I} {J} {K} f g →
    let module f = Idempotent⇒ f
        module g = Idempotent⇒ g
    in record
    { hom = f.hom ∘ g.hom
    ; absorbˡ = begin
      idem K ∘ f.hom ∘ g.hom ≈⟨ pullˡ f.absorbˡ ⟩
      f.hom ∘ g.hom ∎
    ; absorbʳ = begin
      (f.hom ∘ g.hom) ∘ idem I ≈⟨ pullʳ g.absorbʳ ⟩
      f.hom ∘ g.hom ∎
    }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = λ {I} {J} {f} → absorbˡ f
  ; identityʳ = λ {I} {J} {f} → absorbʳ f
  ; identity² = λ {I} → idempotent I
  ; equiv = record
    { refl = refl
    ; sym = λ eq → sym eq
    ; trans = λ eq₁ eq₂ → trans eq₁ eq₂
    }
  ; ∘-resp-≈ = λ eq₁ eq₂ → ∘-resp-≈ eq₁ eq₂
  }
