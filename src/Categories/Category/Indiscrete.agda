{-# OPTIONS --without-K --safe #-}
module Categories.Category.Indiscrete where

-- Category where all arrows are inhabited by a single element
open import Level
open import Data.Unit

open import Categories.Category

open import Relation.Binary.PropositionalEquality as ≡

Indiscrete : ∀ {o ℓ} (A : Set o) → Category o ℓ ℓ
Indiscrete {_} {ℓ} A = record
  { Obj       = A
  ; _⇒_       = λ _ _ → Lift ℓ ⊤
  ; _≈_       = _≡_
  ; id        = _
  ; _∘_       = _
  ; assoc     = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv     = isEquivalence
  ; ∘-resp-≈  = λ where
    refl refl → refl
  }
