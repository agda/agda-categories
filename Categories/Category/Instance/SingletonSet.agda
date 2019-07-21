{-# OPTIONS --without-K --safe #-}

open import Level

-- This is really a degenerate version of Categories.Category.Instance.One
module Categories.Category.Instance.SingletonSet where

open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Category.Instance.Sets
import Categories.Object.Terminal as Term

module _ {o : Level} where
  open Term (Sets o)
  private
    U = Lift o ⊤

  SingletonSet : Set o
  SingletonSet = U

  SingletonSet-⊤ : Terminal
  SingletonSet-⊤ = record { ⊤ = SingletonSet ; !-unique = λ _ → refl }
