{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core
open import Categories.Category.Monoidal.Core

module Categories.Object.Monoid {o ℓ e} {𝒞 : Category o ℓ e} (C : Monoidal 𝒞) where

open import Level

-- a monoid object is a generalization of the idea from algebra of a monoid,
-- extended into any monoidal category

open Category 𝒞
open Monoidal C

record IsMonoid (M : Obj) : Set (ℓ ⊔ e) where
  field
    μ : M ⊗₀ M ⇒ M
    η : unit ⇒ M

  field
    assoc : μ ∘ μ ⊗₁ id ≈ μ ∘ id ⊗₁ μ ∘ associator.from
    identityˡ : unitorˡ.from ≈ μ ∘ η ⊗₁ id
    identityʳ : unitorʳ.from ≈ μ ∘ id ⊗₁ η

record Monoid : Set (o ⊔ ℓ ⊔ e) where
  field
    Carrier : Obj
    isMonoid : IsMonoid Carrier

  open IsMonoid isMonoid public

open Monoid

record Monoid⇒ (M M′ : Monoid) : Set (ℓ ⊔ e) where
  field
    arr : Carrier M ⇒ Carrier M′
    preserves-μ : arr ∘ μ M ≈ μ M′ ∘ arr ⊗₁ arr
    preserves-η : arr ∘ η M ≈ η M′
