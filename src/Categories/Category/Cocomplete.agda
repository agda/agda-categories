{-# OPTIONS --without-K --safe #-}

module Categories.Category.Cocomplete where

open import Level

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Diagram.Colimit using (Colimit)

Cocomplete : (o ℓ e : Level) {o′ ℓ′ e′ : Level} (C : Category o′ ℓ′ e′) → Set _
Cocomplete o ℓ e C = ∀ {J : Category o ℓ e} (F : Functor J C) → Colimit F
