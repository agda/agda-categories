{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Object.Zero

module Experiments.Category.Object.ChainComplex {o ℓ e} {𝒞 : Category o ℓ e} (has-zero : Zero 𝒞) where

open import Level

open import Data.Nat using (ℕ)

open Category 𝒞
open Zero has-zero

