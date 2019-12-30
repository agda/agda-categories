{-# OPTIONS --without-K --safe #-}

module Categories.Enriched.Over.One where

open import Level

open import Categories.Category
-- open import Categories.Category.Monoidal.Instance.Cats using (module Product)
open import Categories.Category.Monoidal.Enriched
open import Categories.Category.Monoidal.Instance.One

TruthValue : (o ℓ e t : Level) → Set (o ⊔ ℓ ⊔ e ⊔ suc t)
TruthValue o ℓ e t = Enriched (One-Monoidal {o} {ℓ} {e}) t
