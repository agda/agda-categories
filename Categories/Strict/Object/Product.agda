{-# OPTIONS --without-K --safe #-}
open import Categories.Strict.Category

--(Binary) product of objects and morphisms

module Categories.Strict.Object.Product {o ℓ} (C : Category o ℓ) where

open import Categories.Strict.Object.Product.Core C public
open import Categories.Strict.Object.Product.Morphisms C public
