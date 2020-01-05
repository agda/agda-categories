{-# OPTIONS --without-K --safe #-}

module Categories.2-Functor where

open import Level

open import Categories.Category.Monoidal.Instance.StrictCats using (module Product)
open import Categories.Enriched.Category using (Category)
open import Categories.Enriched.Functor using (Functor)

module _ {o ℓ e c d} where
  private M = Product.Cats-Monoidal {o} {ℓ} {e}

  2-Functor : Category M c → Category M d → Set (o ⊔ ℓ ⊔ e ⊔ c ⊔ d)
  2-Functor C D = Functor M C D
