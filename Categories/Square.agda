{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- Reasoning facilities about morphism equivalences (not necessarily 'squares')

module Categories.Square {o ℓ e} (C : Category o ℓ e) where

open import Categories.Square.Core C public
open import Categories.Square.Iso C public
