{-# OPTIONS --without-K --safe #-}
module Categories.Category.Discrete where

open import Categories.Category

open import Function
open import Relation.Binary.PropositionalEquality as ≡

{-
 Note that there are two obvious ways of defining ≈ for a Discrete
 Category: either as λ _ _ → ⊤ or as _≡_. The former hand-squashes
 all the proofs of morphisms being the same, while the latter
 explicitly witnesses them. Because this library is proof-relevant,
 the latter choice is more consistent with that philosophy.
-}
Discrete : ∀ {a} (A : Set a) → Category a a a
Discrete A = record
  { Obj       = A
  ; _⇒_       = _≡_
  ; _≈_       = _≡_
  ; id        = refl
  ; _∘_       = flip ≡.trans
  ; assoc     = λ {_ _ _ _ g} → sym (trans-assoc g)
  ; identityˡ = λ {_ _ f} → trans-reflʳ f
  ; identityʳ = refl
  ; equiv     = isEquivalence
  ; ∘-resp-≈  = λ where
    refl refl → refl
  }
