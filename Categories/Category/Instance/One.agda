{-# OPTIONS --without-K --safe #-}

open import Level

module Categories.Category.Instance.One where

open import Data.Unit using (⊤; tt)

open import Categories.Category
open import Categories.Functor
open import Categories.Category.Instance.Cats
import Categories.Object.Terminal as Term

module _ {o ℓ e : Level} where
  open Term (Cats o ℓ e)

  One : Category o ℓ e
  One = record
    { Obj       = Lift o ⊤
    ; _⇒_       = λ _ _ → Lift ℓ ⊤
    ; _≈_       = λ _ _ → Lift e ⊤
    }

  One-⊤ : Terminal
  One-⊤ = record { ⊤ = One }
