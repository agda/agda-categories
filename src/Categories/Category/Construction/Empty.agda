{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Empty {o ℓ e}  where

open import Level
open import Categories.Category.Core
open import Data.Empty.Polymorphic

open Category

-- A level-polymorphic empty category
Empty : Category o ℓ e
Empty .Obj = ⊥
