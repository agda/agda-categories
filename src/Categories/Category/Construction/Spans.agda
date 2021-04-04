{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Construction.Spans {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Category.Diagram.Span 𝒞
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning
open Equiv

open Span
open Span⇒

Spans : Obj → Obj → Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e
Spans X Y = record
  { Obj = Span X Y
  ; _⇒_ = Span⇒
  ; _≈_ = λ f g → arr f ≈ arr g
  ; id = id-span⇒
  ; _∘_ = _∘ₛ_
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≈ = ∘-resp-≈
  }

