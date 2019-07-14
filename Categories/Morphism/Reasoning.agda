{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- Reasoning facilities about morphism equivalences (not necessarily 'squares')

module Categories.Morphism.Reasoning {o ℓ e} (C : Category o ℓ e) where

open import Categories.Morphism.Reasoning.Core C public
open import Categories.Morphism.Reasoning.Iso C public
