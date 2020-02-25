{-# OPTIONS --without-K --safe #-}

open import Level

-- This is really a degenerate version of Categories.Category.Instance.Zero
-- Here EmptySet is not given an explicit name, it is an alias for Lift o ⊥
module Categories.Category.Instance.EmptySet where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Category.Instance.Sets
import Categories.Object.Initial as Init

module _ {o : Level} where
  open Init (Sets o)

  EmptySet-⊥ : Initial
  EmptySet-⊥ = record { ⊥ = Lift o ⊥ ; ! = λ { {A} (lift x) → ⊥-elim x } ; !-unique = λ { f {()} } }
