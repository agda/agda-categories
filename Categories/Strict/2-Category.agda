{-# OPTIONS --without-K --safe #-}

-- A 2-Category is a Category Enriched over the (Weak) Monoidal Category of Strict Categories
module Categories.Strict.2-Category where

open import Level

open import Categories.Strict.Category.Monoidal.Instance.Cats using (module Product)
open import Categories.Category.Monoidal.Enriched

2-Category : (o ℓ t : Level) → Set (suc (o ⊔ ℓ ⊔ t))
2-Category o ℓ t = Enriched ( Product.Cats-Monoidal {o} {ℓ}) t
