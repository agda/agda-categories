{-# OPTIONS --without-K --safe #-}

-- Commutative Monad on a symmetric monoidal category
-- https://ncatlab.org/nlab/show/commutative+monad

module Categories.Monad.Commutative where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong using (StrongMonad; RightStrength; Strength)
open import Categories.Monad.Strong.Properties using (Strength⇒RightStrength)

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} {V : Monoidal C} (S : Symmetric V) where
  record Commutative (LSM : StrongMonad V) : Set (o ⊔ ℓ ⊔ e) where
    open Category C
    open Symmetric S
    open StrongMonad LSM

    rightStrength : RightStrength V M
    rightStrength = Strength⇒RightStrength braided strength

    private
      module LS = Strength strength
      module RS = RightStrength rightStrength
      σ : ∀ {X Y} → X ⊗₀ M.F.₀ Y ⇒ M.F.₀ (X ⊗₀ Y)
      σ {X} {Y} = LS.strengthen.η (X , Y)
      τ : ∀ {X Y} → M.F.₀ X ⊗₀ Y ⇒ M.F.₀ (X ⊗₀ Y)
      τ {X} {Y} = RS.strengthen.η (X , Y)

    field
      commutes : ∀ {X Y} → M.μ.η (X ⊗₀ Y) ∘ M.F.₁ τ ∘ σ ≈ M.μ.η (X ⊗₀ Y) ∘ M.F.₁ σ ∘ τ

  record CommutativeMonad : Set (o ⊔ ℓ ⊔ e) where
    field
      strongMonad : StrongMonad V
      commutative : Commutative strongMonad

    open StrongMonad strongMonad public
    open Commutative commutative public

