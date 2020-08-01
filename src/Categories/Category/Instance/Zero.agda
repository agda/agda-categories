{-# OPTIONS --without-K --safe #-}

open import Level

-- ⊥ is Initial

module Categories.Category.Instance.Zero where

open import Data.Empty using (⊥; ⊥-elim)
open import Function renaming (id to idf)

open import Categories.Category
open import Categories.Functor
open import Categories.Category.Instance.Cats
import Categories.Object.Initial as Init

-- Unlike for ⊤ being Terminal, Agda can't deduce these, need to be explicit
module _ {o ℓ e : Level} where
  open Init (Cats o ℓ e)

  Zero : Category o ℓ e
  Zero = record
    { Obj       = Lift o ⊥
    ; _⇒_       = λ _ _ → Lift ℓ ⊥
    ; _≈_       = λ _ _ → Lift e ⊥
    ; id        = λ { { lift () } }
    ; _∘_       = λ a _ → a -- left-biased rather than strict
    ; assoc     = λ { {lift () } }
    ; sym-assoc = λ { {lift () } }
    ; identityˡ = λ { {()} }
    ; identityʳ = λ { {()} }
    ; identity² = λ { {()} }
    ; ∘-resp-≈  = λ { () }
    ; equiv     = record
      { refl = λ { {()} }
      ; sym = idf
      ; trans = λ a _ → a
      }
    }

  Zero-⊥ : Initial
  Zero-⊥ = record
    { ⊥ = Zero
    ; ⊥-is-initial = record
      { ! = record
        { F₀ = λ { (lift x) → ⊥-elim x }
        ; F₁ = λ { (lift ()) }
        ; identity = λ { {lift ()} }
        ; homomorphism = λ { {lift ()} }
        ; F-resp-≈ = λ { () }
        }
      ; !-unique = λ f → record
        { F⇒G = record { η = λ { () } ; commute = λ { () } ; sym-commute = λ { () } }
        ; F⇐G = record { η = λ { () } ; commute = λ { () } ; sym-commute = λ { () } }
        ; iso = λ { (lift ()) }
        }
      }
    }
