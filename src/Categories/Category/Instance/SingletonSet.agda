{-# OPTIONS --without-K --safe #-}

open import Level

-- This is really a degenerate version of Categories.Category.Instance.One
-- Here SingletonSet is not given an explicit name, it is an alias for ⊤
module Categories.Category.Instance.SingletonSet where

open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Category.Instance.Sets
open import Categories.Category.Instance.Setoids
import Categories.Object.Terminal as Term

module _ {o : Level} where
  open Term (Sets o)

  SingletonSet-⊤ : Terminal
  SingletonSet-⊤ = record { ⊤ = ⊤ ; ⊤-is-terminal = record { !-unique = λ _ _ → refl } }

module _ {c ℓ : Level} where
  open Term (Setoids c ℓ)

  SingletonSetoid : Setoid c ℓ
  SingletonSetoid = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

  SingletonSetoid-⊤ : Terminal
  SingletonSetoid-⊤ = record { ⊤ = SingletonSetoid }
