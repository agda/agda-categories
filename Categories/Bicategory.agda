{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory where

open import Level

open import Categories.Category.Monoidal.Instance.Cats using (module Product)
open import Categories.Category.Monoidal.Enriched

Bicategory : (o ℓ e t : Level) → Set (suc (o ⊔ ℓ ⊔ e ⊔ t))
Bicategory o ℓ e t = Enriched ( Product.Cats-Monoidal {o} {ℓ} {e}) t
