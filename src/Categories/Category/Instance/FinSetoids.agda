{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.FinSetoids where

-- Category of Finite Setoids, as a sub-category of Setoids

open import Level

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ)
open import Function.Bundles using (Inverse)
open import Relation.Binary.Bundles using (module Setoid)
import Relation.Binary.PropositionalEquality as ≡

open import Categories.Category.Core using (Category)
open import Categories.Category.Construction.ObjectRestriction
open import Categories.Category.Instance.Setoids

FinSetoids : (c ℓ : Level) → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
FinSetoids c ℓ = ObjectRestriction (Setoids c ℓ) (λ x → Σ ℕ (λ n → Inverse x (≡.setoid (Fin n))))
