{-# OPTIONS --without-K --safe #-}
module Categories.Strict.Functor.Bifunctor where

-- Bifunctor, aka a Functor from C × D to E
open import Level

open import Categories.Strict.Category
open import Categories.Strict.Functor
open import Categories.Strict.Category.Product

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : Level

Bifunctor : Category o ℓ → Category o′ ℓ′ → Category o″ ℓ″ → Set _
Bifunctor C D E = Functor (Product C D) E
