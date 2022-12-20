{-# OPTIONS --safe --without-K #-}

module Categories.Category.Dagger.Instance.Rels where

open import Categories.Category.Dagger
open import Categories.Category.Instance.Rels

open import Data.Product
open import Function.Base
open import Level
open import Relation.Binary

RelsHasDagger : ∀ {o ℓ} → HasDagger (Rels o ℓ)
RelsHasDagger = record
  { _† = λ R → record
    { fst = flip (proj₁ R)
    ; snd = swap (proj₂ R)
    }
  ; †-identity = λ {A} → record
    { fst = λ y≈x → lift (Setoid.sym A (lower y≈x))
    ; snd = λ x≈y → lift (Setoid.sym A (lower x≈y))
    }
  ; †-homomorphism = record
    { fst = λ { (b , afb , bgc) → b , bgc , afb }
    ; snd = λ { (b , bgc , afb) → b , afb , bgc }
    }
  ; †-resp-≈ = λ f⇔g → record
    { fst = proj₁ f⇔g
    ; snd = proj₂ f⇔g
    }
  ; †-involutive = λ _ → id , id
  }

RelsDagger : ∀ o ℓ → DaggerCategory (suc (o ⊔ ℓ)) (suc (o ⊔ ℓ)) (o ⊔ ℓ)
RelsDagger o ℓ = record
  { C = Rels o ℓ
  ; hasDagger = RelsHasDagger
  }
