{-# OPTIONS --without-K --safe #-}

open import Level

module Categories.Category.Instance.One where

open import Data.Unit using (⊤; tt)

open import Categories.Category
open import Categories.Functor
open import Categories.Category.Instance.Cats
import Categories.Object.Terminal as Term

module _ {o ℓ e : Level} where
  open Term (Cats o ℓ e)
  private
    u = lift {_} {o} tt
    v = lift {_} {ℓ} tt
    w = lift {_} {e} tt


  One : Category o ℓ e
  One = record
    { Obj       = Lift o ⊤
    ; _⇒_       = λ _ _ → Lift ℓ ⊤
    ; _≈_       = λ _ _ → Lift e ⊤
    ; _∘_       = λ _ _ → v
    ; id        = v
    ; assoc     = w
    ; identityˡ = w
    ; identityʳ = w
    ; equiv     = record
      { refl    = w
      ; sym     = λ _ → w
      ; trans   = λ _ _ → w
      }
    ; ∘-resp-≈  = λ _ _ → w
    }

  One-⊤ : Terminal
  One-⊤ = record
    { ⊤        = One
    ; !        = record
      { F₀           = λ _ → u
      ; F₁           = λ _ → v
      ; identity     = w
      ; homomorphism = w
      ; F-resp-≈     = λ _ → w
      }
    ; !-unique = λ F → record
      { F⇒G = record
        { η       = λ _ → v
        ; commute = λ _ → w
        }
      ; F⇐G = record
        { η       = λ _ → v
        ; commute = λ _ → w
        }
      ; iso = λ _ → record
        { isoˡ = w
        ; isoʳ = w
        }
      }
    }
