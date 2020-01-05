{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Cats where

-- The (large) category of (small) categories.
-- Even though Agda can figure out the levels, it is worth making them explicit,
-- to see the large level jumps involved.

open import Level
open import Categories.Category using (Category)
open import Categories.Functor using (Functor; id; _∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; associator; unitorˡ; unitorʳ; unitor²; isEquivalence; _ⓘₕ_; sym)
private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e
    F G H I : Functor C D

Cats : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔  e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Cats o ℓ e = record
  { Obj       = Category o ℓ e
  ; _⇒_       = Functor
  ; _≈_       = NaturalIsomorphism
  ; id        = id
  ; _∘_       = _∘F_
  ; assoc     = λ {_ _ _ _ F G H} → associator F G H
  ; sym-assoc = λ {_ _ _ _ F G H} → sym (associator F G H)
  ; identityˡ = unitorˡ
  ; identityʳ = unitorʳ
  ; identity² = unitor²
  ; equiv     = isEquivalence
  ; ∘-resp-≈  = _ⓘₕ_
  }
