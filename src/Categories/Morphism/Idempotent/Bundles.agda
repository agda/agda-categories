{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

-- Bundled versions of Idempotents, as well as maps between idempotents
module Categories.Morphism.Idempotent.Bundles {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Morphism.Idempotent 𝒞
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning
open Equiv

--------------------------------------------------------------------------------
-- Bundled Idempotents, and maps between them

record BundledIdempotent : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj} : Obj
    isIdempotent : Idempotent obj

  open Idempotent isIdempotent public

open BundledIdempotent

record Idempotent⇒ (I J : BundledIdempotent) : Set (ℓ ⊔ e) where
  private
    module I = BundledIdempotent I
    module J = BundledIdempotent J
  field
    hom : I.obj ⇒ J.obj
    absorbˡ : J.idem ∘ hom ≈ hom
    absorbʳ : hom ∘ I.idem ≈ hom

open Idempotent⇒

--------------------------------------------------------------------------------
-- Identity and Composition of maps between Idempotents

idempotent⇒-id : ∀ {I} → Idempotent⇒ I I
idempotent⇒-id {I} = record
  { hom = idem I
  ; absorbˡ = idempotent I
  ; absorbʳ = idempotent I
  }

idempotent⇒-∘ : ∀ {I J K} → (f : Idempotent⇒ J K) → (g : Idempotent⇒ I J) → Idempotent⇒ I K
idempotent⇒-∘ {I} {J} {K} f g = record
  { hom = f.hom ∘ g.hom
  ; absorbˡ = pullˡ f.absorbˡ
  ; absorbʳ = pullʳ g.absorbʳ
  }
  where
    module f = Idempotent⇒ f
    module g = Idempotent⇒ g
