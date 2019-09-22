{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- The core of a category.
-- See https://ncatlab.org/nlab/show/core

module Categories.Category.Construction.Core {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (_⊔_)
open import Function using (flip)

open import Categories.Category.Groupoid
open import Categories.Morphism 𝒞
open import Categories.Morphism.IsoEquiv 𝒞

open Category 𝒞

Core : Category o (ℓ ⊔ e) e
Core = record
  { Obj       = Obj
  ; _⇒_       = _≅_
  ; _≈_       = _≃_
  ; id        = ≅.refl
  ; _∘_       = flip ≅.trans
  ; assoc     = record { from-≈ = assoc     ; to-≈ = Equiv.sym assoc }
  ; identityˡ = record { from-≈ = identityˡ ; to-≈ = identityʳ }
  ; identityʳ = record { from-≈ = identityʳ ; to-≈ = identityˡ }
  ; equiv     = ≃-isEquivalence
  ; ∘-resp-≈  = λ eq₁ eq₂ → record
      { from-≈ = ∘-resp-≈ (from-≈ eq₁) (from-≈ eq₂)
      ; to-≈   = ∘-resp-≈ (to-≈ eq₂)   (to-≈ eq₁)
      }
  }
  where open _≃_

Core-isGroupoid : Groupoid Core
Core-isGroupoid = record
  { _⁻¹ = ≅.sym
  ; iso = record
    { isoˡ = sym∘ᵢ≃refl
    ; isoʳ = ∘ᵢsym≃refl
    }
  }
  where
    open Category Core renaming (_∘_ to _∘ᵢ_)

    sym∘ᵢ≃refl : ∀ {A B} {f : A ≅ B} → ≅.sym f ∘ᵢ f ≃ ≅.refl
    sym∘ᵢ≃refl {f = f} = record
      { from-≈ = isoˡ
      ; to-≈   = isoˡ
      }
      where open _≅_ f

    ∘ᵢsym≃refl : ∀ {A B} {f : A ≅ B} → f ∘ᵢ ≅.sym f ≃ ≅.refl
    ∘ᵢsym≃refl {f = f} = record
      { from-≈ = isoʳ
      ; to-≈   = isoʳ
      }
      where open _≅_ f
