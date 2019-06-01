{-# OPTIONS --without-K --safe #-}
module Categories.Functor where

open import Level
open import Categories.Category
open import Categories.Functor.Core public
open import Data.Product

open import Relation.Nullary

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′

Faithful : Functor C D → Set _
Faithful {C = C} {D = D} F = ∀ {X Y} → (f g : C [ X , Y ]) → D [ F₁ f ≈ F₁ g ] → C [ f ≈ g ]
  where
  module C = Category C
  module D = Category D
  open Functor F

-- Is this convoluted double-negated definition really necessary? A naive constructive definition of surjectivity
-- requires a right inverse, which would probably restrict the things we can provide proofs for
Full : Functor C D → Set _
Full {C = C} {D = D} F = ∀ {X Y} → ¬ Σ (D [ F₀ X , F₀ Y ]) (λ f → ¬ Σ (C [ X , Y ]) (λ g → D [ F₁ g ≈ f ]))
  where
  module C = Category C
  module D = Category D
  open Functor F

FullyFaithful : Functor C D → Set _
FullyFaithful F = Full F × Faithful F
