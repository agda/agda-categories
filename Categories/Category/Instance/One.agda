{-# OPTIONS --without-K --safe #-}

open import Level

module Categories.Category.Instance.One {o ℓ e : Level} where

open import Categories.Category
open import Categories.Functor
open import Categories.Category.Instance.Cats
open import Categories.Object.Terminal (Cats o ℓ e)

record Unit {x : _} : Set x where
  constructor unit

One : Category o ℓ e
One = record 
  { Obj       = Unit
  ; _⇒_       = λ _ _ → Unit
  ; _≈_       = λ _ _ → Unit
  ; _∘_       = λ _ _ → unit
  ; id        = unit
  ; assoc     = unit
  ; identityˡ = unit
  ; identityʳ = unit
  ; equiv     = record 
    { refl    = unit
    ; sym     = λ _ → unit
    ; trans   = λ _ _ → unit
    }
  ; ∘-resp-≈  = λ _ _ → unit
  }

One-⊤ : Terminal
One-⊤ = record
  { ⊤        = One
  ; !        = record
    { F₀           = λ _ → unit
    ; F₁           = λ _ → unit
    ; identity     = unit
    ; homomorphism = unit
    ; F-resp-≈     = λ _ → unit
    }
  ; !-unique = λ F → record
    { F⇒G = record
      { η       = λ _ → unit
      ; commute = λ _ → unit
      }
    ; F⇐G = record
      { η       = λ _ → unit
      ; commute = λ _ → unit
      }
    ; iso = λ _ → record
      { isoˡ = unit
      ; isoʳ = unit
      }
    }
  }
