{-# OPTIONS --without-K --safe #-}

open import Level

-- This is really a degenerate version of Categories.Category.Instance.One
-- Here SingletonSet is not given an explicit name, it is an alias for Lift o ⊤
module Categories.Category.Instance.SingletonSet where

open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Category.Instance.Sets
import Categories.Object.Terminal as Term

module _ {o : Level} where
  open Term (Sets o)

  SingletonSet-⊤ : Terminal
  SingletonSet-⊤ = record { ⊤ = Lift o ⊤ ; !-unique = λ _ → refl }
