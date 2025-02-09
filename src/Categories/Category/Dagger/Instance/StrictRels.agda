{-# OPTIONS --without-K --safe #-}
module Categories.Category.Dagger.Instance.StrictRels where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Level

open import Categories.Category.Dagger
open import Categories.Category.Instance.StrictRels

StrictRelsHasDagger : ∀ {o ℓ} → HasDagger (StrictRels o ℓ)
StrictRelsHasDagger = record
  { _† = flip
  ; †-identity = (lift ∘ sym ∘ lower) , (lift ∘ sym ∘ lower)
  ; †-homomorphism = (map₂ swap) , (map₂ swap)
  ; †-resp-≈ = λ p → (proj₁ p) , (proj₂ p) -- it's the implicits that need flipped
  ; †-involutive = λ _ → id , id
  }

StrictRelsDagger : ∀ o ℓ → DaggerCategory (suc o) (suc (o ⊔ ℓ)) (o ⊔ ℓ)
StrictRelsDagger o ℓ = record
  { C = StrictRels o ℓ
  ; hasDagger = StrictRelsHasDagger
  }
