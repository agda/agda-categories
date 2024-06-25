{-# OPTIONS --without-K --safe #-}

open import Level
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation.Core

-- define a less-than-great equivalence on natural transformations
module Categories.NaturalTransformation.Equivalence {o ℓ e o′ ℓ′ e′ : Level}
    {C : Category o ℓ e} {D : Category o′ ℓ′ e′} where

module _ {F G : Functor C D} where
  infix 4 _≃_
  open Category.Equiv D

  -- This ad hoc equivalence for NaturalTransformation should really be 'modification'
  --  (yep, tricategories!). What is below is only part of the definition of a 'modification'.  TODO
  _≃_ : Rel (NaturalTransformation F G) (o ⊔ e′)
  _≃_ X Y = ∀ {x} → D [ NaturalTransformation.η X x ≈ NaturalTransformation.η Y x ]

  ≃-isEquivalence : IsEquivalence _≃_
  ≃-isEquivalence = record
    { refl  = refl
    ; sym   = λ f → sym f -- need to eta-expand to get things to line up properly
    ; trans = λ f g → trans f g
    }

≃-setoid : ∀ (F G : Functor C D) → Setoid (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
≃-setoid F G = record
  { Carrier       = NaturalTransformation F G
  ; _≈_           = _≃_
  ; isEquivalence = ≃-isEquivalence
  }
