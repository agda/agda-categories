{-# OPTIONS --without-K --safe #-}

open import Categories.Strict.Category

-- Reasoning facilities about morphism equivalences (not necessarily 'squares')

module Categories.Strict.Morphism.Reasoning {o ℓ} (C : Category o ℓ) where

open import Categories.Strict.Morphism.Reasoning.Core C public
open import Categories.Strict.Morphism.Reasoning.Iso C public
