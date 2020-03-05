{-# OPTIONS --without-K --safe #-}

-- The One Category is also a -2-Category
module Categories.Minus2-Category.Instance.One where

open import Categories.Minus2-Category
open import Categories.Category.Instance.One

-- Proof is trivial
⊤-is-2-Category : ∀ {o ℓ e} → -2-Category {o} {ℓ} {e}
⊤-is-2-Category = record  { cat = One }
