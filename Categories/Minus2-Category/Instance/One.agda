{-# OPTIONS --without-K --safe #-}

-- The One Category is also a -2-Category
module Categories.Minus2-Category.Instance.One where

open import Categories.Minus2-Category
open import Categories.Category.Instance.One

-- Proof is trivial
⊤-is-2-Category : -2-Category
⊤-is-2-Category = record  { cat = One }
