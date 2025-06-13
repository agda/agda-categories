{-# OPTIONS --without-K --safe #-}

-- Commutative Monad on a braided monoidal category
-- https://ncatlab.org/nlab/show/commutative+monad

module Categories.Monad.Commutative where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong using (StrongMonad; RightStrength; Strength)
import Categories.Monad.Strong.Properties as StrongProps

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} {V : Monoidal C} (BV : Braided V) where
  record Commutative (LSM : StrongMonad V) : Set (o ⊔ ℓ ⊔ e) where
    open Category C using (_⇒_; _∘_; _≈_)
    open Braided BV using (_⊗₀_)
    open StrongMonad LSM using (M; strength)
    open StrongProps.Left.Shorthands strength

    rightStrength : RightStrength V M
    rightStrength = StrongProps.Strength⇒RightStrength BV strength

    open StrongProps.Right.Shorthands rightStrength

    field
      commutes : ∀ {X Y} → (M.μ.η (X ⊗₀ Y) ∘ M.F.₁ τ) ∘ σ ≈ (M.μ.η (X ⊗₀ Y) ∘ M.F.₁ σ) ∘ τ


  record CommutativeMonad : Set (o ⊔ ℓ ⊔ e) where
    field
      strongMonad : StrongMonad V
      commutative : Commutative strongMonad

    open StrongMonad strongMonad public
    open Commutative commutative public

