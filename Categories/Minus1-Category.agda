{-# OPTIONS --without-K --safe #-}

module Categories.Minus1-Category where

-- Do it from the ground up: a -1-Category is a Category enriched over -2-Categories
-- The general version is over an arbitrary -2-Category, the strict one over One
open import Level
open import Data.Unit using (⊤; tt)

open import Categories.Minus2-Category
open import Categories.Category.Monoidal.Construction.Minus2
open import Categories.Enriched.Category using (Category)
open import Categories.Category.Monoidal.Instance.One

-1-Category : (t : Level) → (C : -2-Category) → Set (suc t)
-1-Category t C = Category (-2-Monoidal C) t

Strict-1-Category : (t : Level) → Set (suc t)
Strict-1-Category t = Category (One-Monoidal {0ℓ} {0ℓ} {0ℓ}) t
