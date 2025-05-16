{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Zero.Core {o ℓ e}  where

open import Categories.Category.Core using (Category)
open import Data.Empty.Polymorphic using (⊥)

open Category

-- A level-polymorphic empty category
Zero : Category o ℓ e
Zero .Obj = ⊥
