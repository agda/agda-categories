{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.SetoidDiscrete where

open import Data.Unit using (⊤; tt)
open import Function using (flip)
open import Level using (Lift; lift)
open import Relation.Binary using (Setoid; IsEquivalence)

open import Categories.Category.Core using (Category)
open import Categories.Category.Discrete using (DiscreteCategory)
open import Categories.Morphism using (_≅_; ≅-isEquivalence)
{-
 This is a better version of Discrete, which is more in line with
 the rest of this library, and makes a Category out of a Setoid.
 It is still 'wrong' as the equivalence is completely uninformative.
-}

Discrete : ∀ {o ℓ e} (A : Setoid o ℓ) → DiscreteCategory o ℓ e
Discrete {o} {ℓ} {e} A = record
  { category = C
  ; isDiscrete = record
    { isGroupoid = record { _⁻¹ = sym }
    }
  }
  where
    open Setoid A
    C : Category o ℓ e
    C = record
      { Obj       = Carrier
      ; _⇒_       = _≈_
      ; _≈_       = λ _ _ → Lift e ⊤
      ; id        = Setoid.refl A
      ; _∘_       = flip trans
      }
