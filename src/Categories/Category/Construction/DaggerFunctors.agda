{-# OPTIONS --safe --without-K #-}

module Categories.Category.Construction.DaggerFunctors where

open import Categories.Category.Core using (Category)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.SubCategory using (FullSubCategory)
open import Categories.Category.Dagger using (DaggerCategory)
open import Categories.Functor.Dagger using (DaggerFunctor)

open import Level using (Level; _⊔_)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

DaggerFunctors : DaggerCategory o ℓ e → DaggerCategory o′ ℓ′ e′ → Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
DaggerFunctors C D = FullSubCategory (Functors (DaggerCategory.C C) (DaggerCategory.C D)) {I = DaggerFunctor C D} DaggerFunctor.functor
