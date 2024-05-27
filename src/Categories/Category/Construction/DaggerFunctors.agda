{-# OPTIONS --safe --without-K #-}

module Categories.Category.Construction.DaggerFunctors where

open import Categories.Category.Core
open import Categories.Category.Construction.Functors
open import Categories.Category.SubCategory
open import Categories.Category.Dagger
open import Categories.Functor.Dagger

open import Level

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

DaggerFunctors : DaggerCategory o ℓ e → DaggerCategory o′ ℓ′ e′ → Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
DaggerFunctors C D = FullSubCategory (Functors (DaggerCategory.C C) (DaggerCategory.C D)) {I = DaggerFunctor C D} DaggerFunctor.functor

