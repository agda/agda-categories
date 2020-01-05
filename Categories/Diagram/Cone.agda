{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor hiding (id)

-- Cone over a Functor F (from shape category J into category C)

module Categories.Diagram.Cone
  {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where

open Category C
open Functor F

open import Level

record Apex (N : Obj) : Set (ℓ′ ⊔ o′ ⊔ e ⊔ ℓ) where
  field
    ψ       : (X : Category.Obj J) → (N ⇒ F₀ X)
    commute : ∀ {X Y} (f : J [ X , Y ]) → F₁ f ∘ ψ X ≈ ψ Y

record Cone : Set (o ⊔ ℓ′ ⊔ o′ ⊔ e ⊔ ℓ) where
  field
    {N}  : Obj
    apex : Apex N

  open Apex apex public

open Apex
open Cone

record Cone⇒ (c c′ : Cone) : Set (ℓ ⊔ e ⊔ o′) where
  field
    arr     : N c ⇒ N c′
    commute : ∀ {X} → ψ c′ X ∘ arr ≈ ψ c X

open Cone⇒
