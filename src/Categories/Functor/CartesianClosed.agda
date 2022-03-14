{-# OPTIONS --without-K --safe #-}

module Categories.Functor.CartesianClosed where

open import Level

open import Categories.Category.CartesianClosed.Bundle using (CartesianClosedCategory)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Cartesian using (IsCartesianF)

import Categories.Morphism as M

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

record IsCartesianClosedF {C : CartesianClosedCategory o ℓ e} {D : CartesianClosedCategory o′ ℓ′ e′}
  (F : Functor (CartesianClosedCategory.U C) (CartesianClosedCategory.U D)) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module C = CartesianClosedCategory C using (cartesianCategory; cartesianClosed)
    module D = CartesianClosedCategory D using (cartesianCategory; cartesianClosed; _⇒_; _∘_; U)
    module CC = CartesianClosed C.cartesianClosed using (_^_; eval′)
    module DC = CartesianClosed D.cartesianClosed using (_^_; λg)
  field
    F-cartesian : IsCartesianF C.cartesianCategory D.cartesianCategory F
  open Functor F
  open IsCartesianF F-cartesian
  F-mor : ∀ A B → F₀ (A CC.^ B) D.⇒ F₀ A DC.^ F₀ B
  F-mor A B = DC.λg (F₁ CC.eval′ D.∘ ×-iso.to (A CC.^ B) B)
  field
    F-closed : ∀ {A B} → M.IsIso D.U (F-mor A B)


