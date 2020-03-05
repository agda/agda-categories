{-# OPTIONS --without-K --safe #-}
module Categories.Category.SetoidDiscrete where

open import Categories.Category

open import Level
open import Relation.Binary using (Setoid)
open import Function
open import Data.Unit

{-
 This is a better version of Discrete, which is more in line with
 the rest of this library, and makes a Category out of a Setoid.
 But here we have no choice, and we need to truncate the equivalence.
-}

Discrete : ∀ {o ℓ e} (A : Setoid o ℓ) → Category o ℓ e
Discrete {_} {_} {e} A = record
  { Obj       = Carrier
  ; _⇒_       = _≈_
  ; _≈_       = λ _ _ → Lift e ⊤
  ; id        = refl
  ; _∘_       = flip trans
  }
  where
  open Setoid A
