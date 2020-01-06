{-# OPTIONS --without-K --safe #-}

module Categories.2-Functor where

open import Level

open import Categories.Category.Monoidal.Instance.StrictCats using (module Product)
open import Categories.2-Category using (2-Category)
open import Categories.Enriched.Functor using (Functor)

2-Functor : ∀ {o ℓ e c d} →
            2-Category o ℓ e c → 2-Category o ℓ e d → Set (o ⊔ ℓ ⊔ e ⊔ c ⊔ d)
2-Functor C D = Functor (Product.Cats-Monoidal) C D
