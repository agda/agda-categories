{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Finite where

open import Level

open import Categories.Category
open import Categories.Category.Finite renaming (Finite to FiniteC)
open import Categories.Functor

private
  variable
    o ℓ e : Level
    J C : Category o ℓ e

record Finite (F : Functor J C) : Set (levelOfTerm F) where
  field
    finite : FiniteC J

  open FiniteC finite public
