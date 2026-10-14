{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

module Categories.Functor.Slice.BaseChange {o ℓ e} (C : Category o ℓ e) where

open import Categories.Category.CartesianClosed.Locally C using (Locally)
open import Categories.Category.Slice C using (Slice)
open import Categories.Category.Slice.Properties C using (pullback⇒product; slice-slice⇒slice; slice⇒slice-slice)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Slice using (TotalSpace; ConstantFamily; InternalSections)
open import Categories.Diagram.Pullback C using (Pullback)

open Category C

module _ {A B : Obj} (f : B ⇒ A) where

  -- Any morphism induces a functor between slices.
  BaseChange! : Functor (Slice B) (Slice A)
  BaseChange! = TotalSpace (Slice A) ∘F slice⇒slice-slice f

  -- Any morphism which admits pullbacks induces a functor the other way between slices.
  -- This is adjoint to BaseChange!: see Categories.Adjoint.Instance.BaseChange.
  BaseChange* : (∀ {C} {h : C ⇒ A} → Pullback h f) → Functor (Slice A) (Slice B)
  BaseChange* pullback = slice-slice⇒slice f ∘F ConstantFamily (Slice A) (pullback⇒product pullback)

  -- If C is locally Cartesian closed then we get another functor, that is a right adjoint to BaseChange*
  BaseChange⁎ : Locally → Functor (Slice B) (Slice A)
  BaseChange⁎ locally = InternalSections (Slice A) (sliceCCC A) (slice-pullbacks _ _) ∘F slice⇒slice-slice f
    where open Locally locally
