{-# OPTIONS --without-K --safe #-}

-- dual of Span
module Categories.Category.Instance.Cospan where

open import Level
open import Categories.Category
open import Relation.Binary.PropositionalEquality

data CospanObj : Set where
  center : CospanObj
  left   : CospanObj
  right  : CospanObj

data CospanArr : CospanObj → CospanObj → Set where
  cospan-id   : ∀ {o} → CospanArr o o
  cospan-arrˡ : CospanArr left center
  cospan-arrʳ : CospanArr right center

cospan-compose : ∀ {x y z} → CospanArr y z → CospanArr x y → CospanArr x z
cospan-compose cospan-id cospan-id     = cospan-id
cospan-compose cospan-id cospan-arrˡ   = cospan-arrˡ
cospan-compose cospan-id cospan-arrʳ   = cospan-arrʳ
cospan-compose cospan-arrˡ cospan-id   = cospan-arrˡ
cospan-compose cospan-arrʳ cospan-id   = cospan-arrʳ

Cospan : Category 0ℓ 0ℓ 0ℓ
Cospan = record
  { Obj       = CospanObj
  ; _⇒_       = CospanArr
  ; _≈_       = _≡_
  ; id        = cospan-id
  ; _∘_       = cospan-compose
  ; assoc     = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv     = isEquivalence
  ; ∘-resp-≈  = λ { refl refl → refl }
  }
  where assoc : ∀ {x y z w} {f : CospanArr x y} {g : CospanArr y z} {h : CospanArr z w} →
                               cospan-compose (cospan-compose h g) f ≡
                               cospan-compose h (cospan-compose g f)
        assoc {_} {_} {_} {_} {cospan-id} {cospan-id} {cospan-id}       = refl
        assoc {_} {_} {_} {_} {cospan-id} {cospan-id} {cospan-arrˡ}     = refl
        assoc {_} {_} {_} {_} {cospan-id} {cospan-id} {cospan-arrʳ}     = refl
        assoc {_} {_} {_} {_} {cospan-id} {cospan-arrˡ} {cospan-id}     = refl
        assoc {_} {_} {_} {_} {cospan-id} {cospan-arrʳ} {cospan-id}     = refl
        assoc {_} {_} {_} {_} {cospan-arrˡ} {cospan-id} {cospan-id}     = refl
        assoc {_} {_} {_} {_} {cospan-arrʳ} {cospan-id} {cospan-id}     = refl

        identityˡ : ∀ {x y} {f : CospanArr x y} → cospan-compose cospan-id f ≡ f
        identityˡ {_} {_} {cospan-id}   = refl
        identityˡ {_} {_} {cospan-arrˡ} = refl
        identityˡ {_} {_} {cospan-arrʳ} = refl

        identityʳ : ∀ {x y} {f : CospanArr x y} → cospan-compose f cospan-id ≡ f
        identityʳ {_} {_} {cospan-id}   = refl
        identityʳ {_} {_} {cospan-arrˡ} = refl
        identityʳ {_} {_} {cospan-arrʳ} = refl
