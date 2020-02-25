{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor hiding (id)

-- Cocone over a Functor F (from shape category J into category C)

module Categories.Diagram.Cocone
  {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where

open Category C
open Functor F

open import Level

record Coapex (N : Obj) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
  field
    ψ       : (X : Category.Obj J) → F₀ X ⇒ N
    commute : ∀ {X Y} (f : J [ X , Y ]) → ψ Y ∘ F₁ f ≈ ψ X

record Cocone : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
  field
    {N}    : Obj
    coapex : Coapex N

  open Coapex coapex public

open Coapex
open Cocone

record Cocone⇒ (c c′ : Cocone) : Set (ℓ ⊔ e ⊔ o′) where
  field
    arr     : N c ⇒ N c′
    commute : ∀ {X} → arr ∘ ψ c X ≈ ψ c′ X

open Cocone⇒
