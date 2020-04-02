{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Construction.Properties.Presheaves.Complete {o ℓ e} (C : Category o ℓ e) where

open import Categories.Category.Complete
open import Categories.Category.Complete.Finitely
open import Categories.Category.Complete.Properties
open import Categories.Category.Cocomplete
open import Categories.Category.Cocomplete.Finitely
open import Categories.Category.Cocomplete.Properties
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.Properties.Setoids

private
  module C = Category C

Presheaves-Complete : ∀ o′ ℓ′ e′ ℓ″ e″ → Complete o′ ℓ′ e′ (Presheaves C)
Presheaves-Complete o′ ℓ′ e′ ℓ″ e″ = Functors-Complete C.op (Setoids-Complete o′ ℓ′ e′ ℓ″ e″)

Presheaves-FinitelyComplete : ∀ o′ ℓ′ e′ ℓ″ e″ → FinitelyComplete (Presheaves C)
Presheaves-FinitelyComplete o′ ℓ′ e′ ℓ″ e″ = Complete⇒FinitelyComplete (Presheaves C) (Presheaves-Complete o′ ℓ′ e′ ℓ″ e″)

Presheaves-Cocomplete : ∀ o′ ℓ′ e′ ℓ″ e″ → Cocomplete o′ ℓ′ e′ (Presheaves C)
Presheaves-Cocomplete o′ ℓ′ e′ ℓ″ e″ = Functors-Cocomplete C.op (Setoids-Cocomplete o′ ℓ′ e′ ℓ″ e″)

Presheaves-FinitelyCocomplete : ∀ o′ ℓ′ e′ ℓ″ e″ → FinitelyCocomplete (Presheaves C)
Presheaves-FinitelyCocomplete o′ ℓ′ e′ ℓ″ e″ = Cocomplete⇒FinitelyCocomplete (Presheaves C) (Presheaves-Cocomplete o′ ℓ′ e′ ℓ″ e″)
