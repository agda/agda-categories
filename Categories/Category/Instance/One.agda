{-# OPTIONS --without-K --safe #-}

open import Level

module Categories.Category.Instance.One {o ℓ e : Level} where

open import Categories.Category
open import Categories.Functor
open import Categories.Category.Instance.Cats
open import Categories.Object.Terminal (Cats o ℓ e)

record Unit {x : _} : Set x where
  constructor unit

One : Category o ℓ e
One = record
  { Obj       = Unit
  ; _⇒_       = λ _ _ → Unit
  ; _≈_       = λ _ _ → Unit
  }

One-⊤ : Terminal
One-⊤ = record
  { ⊤        = One
  }
