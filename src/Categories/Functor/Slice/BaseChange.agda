{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

module Categories.Functor.Slice.BaseChange {o ℓ e} (C : Category o ℓ e) where

open import Categories.Category.Slice C using (Slice)
open import Categories.Category.Slice.Properties C using (pullback⇒product; slice-slice⇒slice; slice⇒slice-slice)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Slice using (Forgetful; Free)
open import Categories.Diagram.Pullback C using (Pullback)

open Category C

module _ {A B : Obj} (f : B ⇒ A) where

  -- Any morphism induces a functor between slices.
  BaseChange! : Functor (Slice B) (Slice A)
  BaseChange! = Forgetful (Slice A) ∘F slice⇒slice-slice f

  -- Any morphism which admits pullbacks induces a functor the other way between slices.
  -- This is adjoint to BaseChange!: see Categories.Adjoint.Instance.BaseChange.
  BaseChange* : (∀ {C} {h : C ⇒ A} → Pullback f h) → Functor (Slice A) (Slice B)
  BaseChange* pullback = slice-slice⇒slice f ∘F Free (Slice A) (pullback⇒product pullback)
