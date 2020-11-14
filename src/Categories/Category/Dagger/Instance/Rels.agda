{-# OPTIONS --without-K --safe #-}
module Categories.Category.Dagger.Instance.Rels where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Level

open import Categories.Category.Dagger
open import Categories.Category.Instance.Rels

RelsHasDagger : ∀ {o ℓ} → HasDagger (Rels o ℓ)
RelsHasDagger = record
  { _† = flip
  ; †-identity = λ _ _ → (λ p → lift (sym (lower p))) , λ p → lift (sym (lower p))
  ; †-homomorphism = λ _ _ → map₂ swap , map₂ swap
  ; †-resp-≈ = flip
  ; †-involutive = λ _ _ _ → id , id
  }

RelsDagger : ∀ o ℓ → DaggerCategory (suc o) (suc (o ⊔ ℓ)) (o ⊔ ℓ)
RelsDagger o ℓ = record
  { C = Rels o ℓ
  ; hasDagger = RelsHasDagger
  }
