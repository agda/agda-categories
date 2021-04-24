{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; _[_,_]; _[_∘_]; _[_≈_])

-- Bundled versions of Idempotents, as well as maps between idempotents.
module Categories.Morphism.Idempotent.Bundles {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

import Categories.Morphism.Idempotent 𝒞 as Idem
open import Categories.Morphism.Reasoning 𝒞

private
  module 𝒞 = Category 𝒞
  open 𝒞.HomReasoning
  open 𝒞.Equiv

--------------------------------------------------------------------------------
-- Bundled Idempotents, and maps between them

record Idempotent : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj} : 𝒞.Obj
    isIdempotent : Idem.Idempotent obj

  open Idem.Idempotent isIdempotent public

open Idempotent

record Idempotent⇒ (I J : Idempotent) : Set (ℓ ⊔ e) where
  private
    module I = Idempotent I
    module J = Idempotent J
  field
    hom     : 𝒞 [ I.obj , J.obj ]
    absorbˡ : 𝒞 [ 𝒞 [ J.idem ∘ hom ] ≈ hom ]
    absorbʳ : 𝒞 [ 𝒞 [ hom ∘ I.idem ] ≈ hom ]

open Idempotent⇒

--------------------------------------------------------------------------------
-- Identity and Composition of maps between Idempotents

id : ∀ {I} → Idempotent⇒ I I
id {I} = record
  { hom = idem I
  ; absorbˡ = idempotent I
  ; absorbʳ = idempotent I
  }

_∘_ : ∀ {I J K} → (f : Idempotent⇒ J K) → (g : Idempotent⇒ I J) → Idempotent⇒ I K
_∘_ {I} {J} {K} f g = record
  { hom = 𝒞 [ f.hom ∘ g.hom ]
  ; absorbˡ = pullˡ f.absorbˡ
  ; absorbʳ = pullʳ g.absorbʳ
  }
  where
    module f = Idempotent⇒ f
    module g = Idempotent⇒ g
