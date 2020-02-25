{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Monad

module Categories.Monad.Idempotent {o ℓ e} {C : Category o ℓ e} (M : Monad C) where

open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Equivalence
open import Categories.Functor

private
  module M = Monad M

open NaturalTransformation

record Idempotent : Set (o ⊔ ℓ ⊔ e) where
  field
    Fη≡ηF : ∀ X → C [ η (M.F ∘ˡ M.η) X ≈ η (M.η ∘ʳ M.F) X ]
