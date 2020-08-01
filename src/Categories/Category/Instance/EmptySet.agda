{-# OPTIONS --without-K --safe #-}

open import Level

-- This is really a degenerate version of Categories.Category.Instance.Zero
-- Here EmptySet is not given an explicit name, it is an alias for Lift o ⊥
module Categories.Category.Instance.EmptySet where

open import Data.Unit
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Equality using (Π)
open Π using (_⟨$⟩_)

open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Category.Instance.Sets
open import Categories.Category.Instance.Setoids
import Categories.Object.Initial as Init

module _ {o : Level} where
  open Init (Sets o)

  EmptySet-⊥ : Initial
  EmptySet-⊥ = record { ⊥ = Lift o ⊥ ; ⊥-is-initial = record { ! = λ { {A} (lift x) → ⊥-elim x } ; !-unique = λ { f {()} } } }

module _ {c ℓ : Level} where
  open Init (Setoids c ℓ)

  EmptySetoid : Setoid c ℓ
  EmptySetoid = record
    { Carrier = Lift c ⊥
    ; _≈_     = λ _ _ → Lift ℓ ⊤
    }

  EmptySetoid-⊥ : Initial
  EmptySetoid-⊥ = record
    { ⊥            = EmptySetoid
    ; ⊥-is-initial = record
      { !        = record
        { _⟨$⟩_ = λ { () }
        ; cong  = λ { {()} }
        }
      ; !-unique = λ { _ {()} }
      }
    }
