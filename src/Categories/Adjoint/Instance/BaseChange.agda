{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

module Categories.Adjoint.Instance.BaseChange {o ℓ e} (C : Category o ℓ e) where

open import Categories.Adjoint using (_⊣_)
open import Categories.Adjoint.Compose using (_∘⊣_)
open import Categories.Adjoint.Properties using (⊣×≃⇒⊣)
open import Categories.Adjoint.Instance.Slice using (TotalSpace⊣ConstantFamily; ConstantFamily⊣InternalSections)
open import Categories.Category.CartesianClosed.Locally using (Locally)
open import Categories.Category.Slice C using (Slice; sliceobj)
open import Categories.Category.Slice.Properties C using (pullback⇒product; slice-slice≃slice)
open import Categories.Category.Equivalence.Properties using (module C≅D)
open import Categories.Diagram.Pullback C using (Pullback)
open import Categories.Functor.Slice using (ConstantFamily; ConstantFamily-prop; InternalSections)
open import Categories.Functor.Slice.BaseChange C using (BaseChange!; BaseChange*; BaseChange⁎)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; refl)

open Category C

module _ {A B : Obj} (f : B ⇒ A) where

  !⊣* : (pullback : ∀ {C} {h : C ⇒ A} → Pullback h f) → BaseChange! f ⊣ BaseChange* f pullback
  !⊣* pullback = C≅D.L⊣R (slice-slice≃slice f) ∘⊣ TotalSpace⊣ConstantFamily (Slice A) (pullback⇒product pullback)

  *⊣⁎ : (locally : Locally C) → BaseChange* f (Locally.pullbacks locally _ _) ⊣ BaseChange⁎ f locally
  *⊣⁎ locally = lhs₂ ∘⊣ C≅D.R⊣L (slice-slice≃slice f)
    where
      open Locally locally

      lhs₁ : ConstantFamily (Slice A) {sliceobj f} (sliceProd.product A) ⊣ InternalSections (Slice A) (sliceCCC A) (slice-pullbacks _ _)
      lhs₁ = ConstantFamily⊣InternalSections (Slice A) (sliceCCC A) (slice-pullbacks _ _)

      transform : ConstantFamily (Slice A) {sliceobj f} (sliceProd.product A) ≃ ConstantFamily (Slice A) {sliceobj f} (pullback⇒product (pullbacks _ f))
      transform = ConstantFamily-prop (Slice A) (sliceProd.product A) (pullback⇒product (pullbacks _ f))

      lhs₂ : ConstantFamily (Slice A) {sliceobj f} (pullback⇒product (pullbacks _ f)) ⊣ InternalSections (Slice A) (sliceCCC A) (slice-pullbacks _ _)
      lhs₂ = ⊣×≃⇒⊣ lhs₁ transform refl
