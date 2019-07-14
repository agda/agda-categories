{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Presheaf where

open import Categories.Category
open import Categories.Functor

Presheaf : ∀ {o ℓ e} {o′ ℓ′ e′} (C : Category o ℓ e) (V : Category o′ ℓ′ e′) → Set _
Presheaf C V = Functor C.op V
  where module C = Category C
