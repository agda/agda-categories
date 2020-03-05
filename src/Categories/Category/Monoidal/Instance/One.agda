{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Instance.One where

open import Level
open import Data.Unit using (⊤; tt)

open import Categories.Category
open import Categories.Category.Instance.One
open import Categories.Category.Monoidal
open import Categories.Functor.Bifunctor
open import Categories.Morphism using (_≅_)

-- That One is monoidal is so easy to prove that Agda can do it all on its own!
One-Monoidal : {o ℓ e : Level} → Monoidal (One {o} {ℓ} {e})
One-Monoidal = _
