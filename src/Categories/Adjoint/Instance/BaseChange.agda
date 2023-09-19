{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

module Categories.Adjoint.Instance.BaseChange {o ℓ e} (C : Category o ℓ e) where

open import Categories.Adjoint using (_⊣_)
open import Categories.Adjoint.Compose using (_∘⊣_)
open import Categories.Adjoint.Instance.Slice using (Forgetful⊣Free)
open import Categories.Category.Slice C using (Slice)
open import Categories.Category.Slice.Properties C using (pullback⇒product; slice-slice≃slice)
open import Categories.Category.Equivalence.Properties using (module C≅D)
open import Categories.Diagram.Pullback C using (Pullback)
open import Categories.Functor.Slice.BaseChange C using (BaseChange!; BaseChange*)

open Category C

module _ {A B : Obj} (f : B ⇒ A) (pullback : ∀ {C} {h : C ⇒ A} → Pullback f h) where

  !⊣* : BaseChange! f ⊣ BaseChange* f pullback
  !⊣* = C≅D.L⊣R (slice-slice≃slice f) ∘⊣ Forgetful⊣Free (Slice A) (pullback⇒product pullback)
