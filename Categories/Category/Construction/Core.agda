{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- The core of a category.
-- See https://ncatlab.org/nlab/show/core

module Categories.Category.Construction.Core {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (_⊔_)
open import Function using (flip)

open import Categories.Category.Groupoid using (Groupoid; IsGroupoid)
open import Categories.Morphism 𝒞
open import Categories.Morphism.IsoEquiv 𝒞

open Category 𝒞
open _≃_

Core : Category o (ℓ ⊔ e) e
Core = record
  { Obj       = Obj
  ; _⇒_       = _≅_
  ; _≈_       = _≃_
  ; id        = ≅.refl
  ; _∘_       = flip ≅.trans
  ; assoc     = ⌞ assoc     ⌟
  ; sym-assoc = ⌞ sym-assoc ⌟
  ; identityˡ = ⌞ identityˡ ⌟
  ; identityʳ = ⌞ identityʳ ⌟
  ; identity² = ⌞ identity² ⌟
  ; equiv     = ≃-isEquivalence
  ; ∘-resp-≈  = λ where ⌞ eq₁ ⌟ ⌞ eq₂ ⌟ → ⌞ ∘-resp-≈ eq₁ eq₂ ⌟
  }

Core-isGroupoid : IsGroupoid Core
Core-isGroupoid = record
  { _⁻¹ = ≅.sym
  ; iso = λ {_ _ f} → record { isoˡ = ⌞ isoˡ f ⌟ ; isoʳ = ⌞ isoʳ f ⌟ }
  }
  where open _≅_

CoreGroupoid : Groupoid o (ℓ ⊔ e) e
CoreGroupoid = record { category = Core; isGroupoid = Core-isGroupoid }
