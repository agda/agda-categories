{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

module Categories.Category.Construction.KaroubiEnvelope {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning
open Equiv

record Idempotent : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj} : Obj
    idem  : obj ⇒ obj
    idempotent : idem ∘ idem ≈ idem

record Idempotent⇒ (I J : Idempotent) : Set (ℓ ⊔ e) where
  private
    module I = Idempotent I
    module J = Idempotent J
  field
    hom : I.obj ⇒ J.obj
    absorbˡ : J.idem ∘ hom ≈ hom
    absorbʳ : hom ∘ I.idem ≈ hom

open Idempotent
open Idempotent⇒

KaroubiEnvelope : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
KaroubiEnvelope = record
  { Obj = Idempotent
  ; _⇒_ = Idempotent⇒
  ; _≈_ = λ f g → Idempotent⇒.hom f ≈ Idempotent⇒.hom g
  ; id = λ {I} →
    let module I = Idempotent I
    in record
      { hom = I.idem
      ; absorbˡ = I.idempotent
      ; absorbʳ = I.idempotent
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
