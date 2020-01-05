{-# OPTIONS --without-K --safe #-}
module Categories.Category.Discrete where

open import Categories.Category

open import Function
open import Relation.Binary.PropositionalEquality as ≡

Discrete : ∀ {a} (A : Set a) → Category a a a
Discrete A = record
  { Obj       = A
  ; _⇒_       = _≡_
  ; _≈_       = _≡_
  ; id        = refl
  ; _∘_       = flip ≡.trans
  ; assoc     = λ {_ _ _ _ g} → sym (trans-assoc g)
  ; sym-assoc = λ {_ _ _ _ g} → trans-assoc g
  ; identityˡ = λ {_ _ f} → trans-reflʳ f
  ; identityʳ = refl
  ; identity² = refl
  ; equiv     = isEquivalence
  ; ∘-resp-≈  = λ where
    refl refl → refl
  }
