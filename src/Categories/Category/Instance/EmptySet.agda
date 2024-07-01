{-# OPTIONS --without-K --safe #-}

open import Level

-- This is really a degenerate version of Categories.Category.Instance.Zero
-- Here EmptySet is not given an explicit name, it is an alias for Lift o ⊥
module Categories.Category.Instance.EmptySet where

open import Data.Empty.Polymorphic using (⊥; ⊥-elim)

open import Relation.Binary using (Setoid)

open import Categories.Category.Instance.Sets
open import Categories.Category.Instance.Setoids
import Categories.Object.Initial as Init

module _ {o : Level} where
  open Init (Sets o)

  EmptySet-⊥ : Initial
  EmptySet-⊥ .Initial.⊥ = ⊥
  EmptySet-⊥ .Initial.⊥-is-initial .IsInitial.! ()

module _ {c ℓ : Level} where
  open Init (Setoids c ℓ)

  EmptySetoid : Setoid c ℓ
  EmptySetoid = record
    { Carrier = ⊥
    ; _≈_     = λ ()
    ; isEquivalence = record { refl = λ { {()} } ; sym = λ { {()} }  ; trans = λ { {()} } }
    }

  EmptySetoid-⊥ : Initial
  EmptySetoid-⊥ = record
    { ⊥            = EmptySetoid
    ; ⊥-is-initial = record
      { !        = record
        { to = λ ()
        ; cong  = λ { {()} }
        }
      ; !-unique = λ { _ {()} }
      }
    }
