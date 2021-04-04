{-# OPTIONS --without-K --safe #-}
module Categories.Category.Species where

-- The Category of Species, as the Functor category from Core (FinSetoids) to Setoids.
-- Setoids used here because that's what fits best in this setting.
-- The constructions of the theory of Species are in Species.Construction

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Construction.Functors
open import Categories.Category.Construction.Core using (Core)
open import Categories.Category.Instance.FinSetoids using (FinSetoids)
open import Categories.Category.Instance.Setoids using (Setoids)

private
  variable
    o ℓ o′ ℓ′ : Level

-- note how Species, as a category, raises levels.
Species : (o ℓ o′ ℓ′ : Level) → Category (suc (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)) (suc (o ⊔ ℓ) ⊔ (o′ ⊔ ℓ′)) (suc (o ⊔ ℓ) ⊔ o′ ⊔ ℓ′)
Species o ℓ o′ ℓ′ = Functors (Core (FinSetoids o ℓ)) (Setoids o′ ℓ′)
