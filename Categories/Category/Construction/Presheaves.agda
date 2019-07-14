{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Presheaves where

-- The Category of Presheaves over a Category C, i.e.
-- the Functor Category [ C.op , Setoids ]
-- Again, the levels are made explicit to show the generality and constraints.
open import Level

open import Categories.Category
open import Categories.Category.Construction.Functors
open import Categories.Category.Instance.Setoids using (Setoids)

Presheaves : ∀ {o ℓ ℓ′ e e′ : Level} → Category o ℓ e →
  Category (o ⊔ ℓ ⊔ e ⊔ suc (ℓ′ ⊔ e′)) (o ⊔ ℓ ⊔ e ⊔ suc (ℓ′ ⊔ e′)) (o ⊔ ℓ′ ⊔ e′)
Presheaves {o} {ℓ} {ℓ′} {e} {e′} C = Functors (Category.op C) (Setoids ℓ′ e′)
