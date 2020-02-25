{-# OPTIONS --without-K --safe #-}

module Categories.Enriched.Over.One where

open import Level

open import Categories.Category.Monoidal.Instance.One
open import Categories.Enriched.Category

TruthValue : (o ℓ e t : Level) → Set (o ⊔ ℓ ⊔ e ⊔ suc t)
TruthValue o ℓ e t = Category (One-Monoidal {o} {ℓ} {e}) t
