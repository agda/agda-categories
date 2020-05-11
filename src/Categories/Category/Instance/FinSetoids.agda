{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.FinSetoids where

-- Category of Finite Setoids, as a sub-category of Setoids

open import Level

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ)
open import Function.Bundles using (Inverse)
open import Relation.Unary using (Pred)
open import Relation.Binary.Bundles using (Setoid; module Setoid)
import Relation.Binary.PropositionalEquality as ≡

open import Categories.Category.Core using (Category)
open import Categories.Category.Construction.ObjectRestriction
open import Categories.Category.Instance.Setoids

-- The predicate that will be used
IsFiniteSetoid : {c ℓ : Level} → Pred (Setoid c ℓ) (c ⊔ ℓ)
IsFiniteSetoid X = Σ ℕ (λ n → Inverse X (≡.setoid (Fin n)))

-- The actual Category
FinSetoids : (c ℓ : Level) → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
FinSetoids c ℓ = ObjectRestriction (Setoids c ℓ) IsFiniteSetoid
