{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Level

module Categories.Object.StrictInitial {o ℓ e} (C : Category o ℓ e) where

open Category C
open import Categories.Morphism C using (Epi; _≅_)
open import Categories.Object.Initial C

record IsStrictInitial (⊥ : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    is-initial : IsInitial ⊥
  open IsInitial is-initial public

  field
    is-strict : ∀ {A} → A ⇒ ⊥ → A ≅ ⊥

open IsStrictInitial

record StrictInitial  : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊥ : Obj
    is-strict-initial : IsStrictInitial ⊥

  initial : Initial
  initial .Initial.⊥ = ⊥
  initial .Initial.⊥-is-initial = is-strict-initial .is-initial

  open Initial initial public
