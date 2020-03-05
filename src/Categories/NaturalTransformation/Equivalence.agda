{-# OPTIONS --without-K --safe #-}

-- define a less-than-great equivalence on natural transformations
module Categories.NaturalTransformation.Equivalence where

open import Level
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation.Core

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D E : Category o ℓ e

-- This ad hoc equivalence for NaturalTransformation should really be 'modification'
--  (yep, tricategories!). What is below is only part of the definition of a 'modification'.  TODO
infix 4 _≃_

_≃_ : ∀ {F G : Functor C D} → Rel (NaturalTransformation F G) _
_≃_ {D = D} X Y = ∀ {x} → D [ NaturalTransformation.η X x ≈ NaturalTransformation.η Y x ]

≃-isEquivalence : ∀ {F G : Functor C D} → IsEquivalence (_≃_ {F = F} {G})
≃-isEquivalence {D = D} {F} {G} = record
  { refl  = refl
  ; sym   = λ f → sym f -- need to eta-expand to get things to line up properly
  ; trans = λ f g → trans f g
  }
  where open Category.Equiv D

≃-setoid : ∀ (F G : Functor C D) → Setoid _ _
≃-setoid F G = record
  { Carrier       = NaturalTransformation F G
  ; _≈_           = _≃_
  ; isEquivalence = ≃-isEquivalence
  }
