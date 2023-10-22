{-# OPTIONS --without-K --safe #-}

-- Commutative Monad on a symmetric monoidal category
-- https://ncatlab.org/nlab/show/commutative+monad

module Categories.Monad.Commutative where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Core
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Monad
open import Categories.Monad.Strong

private
  variable
    o ℓ e : Level

record CommutativeMonad {C : Category o ℓ e} (V : Monoidal C) (S : Symmetric V) (T : StrongMonad V) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  open Symmetric S
  open StrongMonad T


  σ : ∀ {X Y} → X ⊗₀ M.F.₀ Y ⇒ M.F.₀ (X ⊗₀ Y)
  σ {X} {Y} = strengthen.η (X , Y)

  τ : ∀ {X Y} → M.F.₀ X ⊗₀ Y ⇒ M.F.₀ (X ⊗₀ Y)
  τ {X} {Y} = M.F.₁ (braiding.⇐.η (X , Y)) ∘ σ ∘ braiding.⇒.η (M.F.₀ X , Y)

  field
    commutes : ∀ {X Y} → M.μ.η (X ⊗₀ Y) ∘ M.F.₁ τ ∘ σ ≈ M.μ.η (X ⊗₀ Y) ∘ M.F.₁ σ ∘ τ