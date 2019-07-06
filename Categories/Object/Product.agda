{-# OPTIONS --without-K --safe #-}
open import Categories.Category

--(Binary) product of objects and morphisms

module Categories.Object.Product {o ℓ e} (C : Category o ℓ e) where

open import Categories.Object.Product.Core C public
open import Categories.Object.Product.Morphisms C public
