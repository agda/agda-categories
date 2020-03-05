{-# OPTIONS --without-K --safe #-}

-- https://ncatlab.org/nlab/show/span
-- The colimit of a functor from this category is a pushout in the target category.
module Categories.Category.Instance.Span where

open import Level
open import Categories.Category
open import Relation.Binary.PropositionalEquality

data SpanObj : Set where
  center : SpanObj
  left   : SpanObj
  right  : SpanObj

data SpanArr : SpanObj → SpanObj → Set where
  span-id   : ∀ {o} → SpanArr o o
  span-arrˡ : SpanArr center left
  span-arrʳ : SpanArr center right

span-compose : ∀ {x y z} → SpanArr y z → SpanArr x y → SpanArr x z
span-compose span-id span-id   = span-id
span-compose span-id span-arrˡ = span-arrˡ
span-compose span-id span-arrʳ = span-arrʳ
span-compose span-arrˡ span-id = span-arrˡ
span-compose span-arrʳ span-id = span-arrʳ

Span : Category 0ℓ 0ℓ 0ℓ
Span = record
  { Obj       = SpanObj
  ; _⇒_       = SpanArr
  ; _≈_       = _≡_
  ; id        = span-id
  ; _∘_       = span-compose
  ; assoc     = assoc
  ; sym-assoc = sym assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = λ {x} → identity² {x}
  ; equiv     = isEquivalence
  ; ∘-resp-≈  = λ { refl refl → refl }
  }
  where assoc : ∀ {x y z w} {f : SpanArr x y} {g : SpanArr y z} {h : SpanArr z w} →
                               span-compose (span-compose h g) f ≡
                               span-compose h (span-compose g f)
        assoc {_} {_} {_} {_} {span-id} {span-id} {span-id}   = refl
        assoc {_} {_} {_} {_} {span-id} {span-id} {span-arrˡ} = refl
        assoc {_} {_} {_} {_} {span-id} {span-id} {span-arrʳ} = refl
        assoc {_} {_} {_} {_} {span-id} {span-arrˡ} {span-id} = refl
        assoc {_} {_} {_} {_} {span-id} {span-arrʳ} {span-id} = refl
        assoc {_} {_} {_} {_} {span-arrˡ} {span-id} {span-id} = refl
        assoc {_} {_} {_} {_} {span-arrʳ} {span-id} {span-id} = refl

        identityˡ : ∀ {x y} {f : SpanArr x y} → span-compose span-id f ≡ f
        identityˡ {_} {_} {span-id}   = refl
        identityˡ {_} {_} {span-arrˡ} = refl
        identityˡ {_} {_} {span-arrʳ} = refl

        identityʳ : ∀ {x y} {f : SpanArr x y} → span-compose f span-id ≡ f
        identityʳ {_} {_} {span-id}   = refl
        identityʳ {_} {_} {span-arrˡ} = refl
        identityʳ {_} {_} {span-arrʳ} = refl

        identity² : {x : SpanObj} → span-compose span-id span-id ≡ span-id
        identity² = refl
