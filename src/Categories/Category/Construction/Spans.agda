{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- The 1-Category of Spans
module Categories.Category.Construction.Spans {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning
open Equiv

record Span (X Y : Obj) : Set (o ⊔ ℓ) where
  field
    M : Obj
    dom : M ⇒ X
    cod : M ⇒ Y

open Span

record Span⇒ {X Y} (f g : Span X Y) : Set (o ⊔ ℓ ⊔ e) where
  field
    arr : M f ⇒ M g
    commute-dom : dom g ∘ arr ≈ dom f
    commute-cod : cod g ∘ arr ≈ cod f

open Span⇒

Spans : Obj → Obj → Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e
Spans X Y = record
  { Obj = Span X Y
  ; _⇒_ = Span⇒
  ; _≈_ = λ f g → arr f ≈ arr g
  ; id = record
    { arr = id
    ; commute-dom = identityʳ
    ; commute-cod = identityʳ
    }
  ; _∘_ = λ {f g h} α β → record
    { arr = arr α ∘ arr β
    ; commute-dom = begin
      dom h ∘ arr α ∘ arr β ≈⟨ pullˡ (commute-dom α) ⟩
      dom g ∘ arr β ≈⟨ commute-dom β ⟩
      dom f ∎
    ; commute-cod = begin
      cod h ∘ arr α ∘ arr β ≈⟨ pullˡ (commute-cod α) ⟩
      cod g ∘ arr β ≈⟨ commute-cod β ⟩
      cod f ∎
    }
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
