{-# OPTIONS --without-K --safe #-}

module Categories.2-Category where

open import Level

open import Categories.Category.Monoidal.Instance.StrictCats using (module Product)
open import Categories.Enriched.Category renaming (Category to Enriched)

2-Category : (o ℓ e t : Level) → Set (suc (o ⊔ ℓ ⊔ e ⊔ t))
2-Category o ℓ e t = Enriched (Product.Cats-Monoidal {o} {ℓ} {e}) t
