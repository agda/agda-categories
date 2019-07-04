{-# OPTIONS --without-K --safe #-}
module Categories.Category.Cats where

open import Level
open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism
import Categories.Morphism as M
import Categories.Square as Square

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e
    F G H I : Functor C D

Cats : ∀ o ℓ e → Category _ _ _
Cats o ℓ e = record
  { Obj       = Category o ℓ e
  ; _⇒_       = Functor
  ; _≈_       = NaturalIsomorphism
  ; id        = id
  ; _∘_       = _∘F_
  ; assoc     = λ {_ _ _ _ F G H} → associator F G H
  ; identityˡ = unitorˡ
  ; identityʳ = unitorʳ
  ; equiv     = λ {A B} → isEquivalence A B
  ; ∘-resp-≈  = _ⓘₕ_
  }
