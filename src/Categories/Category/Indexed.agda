{-# OPTIONS --without-K --safe #-}
module Categories.Category.Indexed where

-- Definition of an 'Indexed Category'
--  https://ncatlab.org/nlab/show/indexed+category

-- It should be abundantly clear that this is a horrible name.
-- Indeed, the nLab says that it's a "2-presheaf" is much more
-- accurate.

open import Level

open import Categories.Bicategory using (Bicategory)
open import Categories.Bicategory.Opposite using (op)
open import Categories.Bicategory.Instance.Cats using (Cats)
open import Categories.Pseudofunctor using (Pseudofunctor)

IndexedCategory : ∀ {ℓ e b o} → (C : Bicategory ℓ e b o) → Set (suc (o ⊔ ℓ ⊔ e) ⊔ b)
IndexedCategory {ℓ} {e} {b} {o} C = Pseudofunctor (op C) (Cats o ℓ e)
