{-# OPTIONS --without-K --safe #-}

-- Commutative Monad on a braided monoidal category
-- https://ncatlab.org/nlab/show/commutative+monad

module Categories.Monad.Commutative where

open import Level using (Level; _⊔_)
open import Data.Product using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong using (StrongMonad; RightStrength; Strength)
import Categories.Monad.Strong.Properties as StrongProps
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} {V : Monoidal C} (BV : Braided V) where
  record Commutative (LSM : StrongMonad V) : Set (o ⊔ ℓ ⊔ e) where
    open Category C using (_⇒_; _∘_; _≈_; module HomReasoning; module Equiv)
    open Braided BV using (_⊗₀_)
    open StrongMonad LSM using (M; strength)
    open StrongProps.Left.Shorthands strength
    open BraidedProps.Shorthands BV renaming (σ to B; σ⇒ to B⇒; σ⇐ to B⇐)

    rightStrength : RightStrength V M
    rightStrength = StrongProps.Strength⇒RightStrength BV strength

    open StrongProps.Right.Shorthands rightStrength

    field
      commutes : ∀ {X Y} → (M.μ.η (X ⊗₀ Y) ∘ M.F.₁ τ) ∘ σ ≈ (M.μ.η (X ⊗₀ Y) ∘ M.F.₁ σ) ∘ τ

    σ-τ : ∀ {X} {Y} → σ {X} {Y} ≈ M.F.₁ B⇒ ∘ τ ∘ B⇐
    σ-τ = begin 
      σ                                   ≈˘⟨ cancelʳ (Braided.braiding.iso.isoʳ BV _) ⟩ 
      (σ ∘ B⇒) ∘ B⇐                       ≈˘⟨ pullˡ (cancelˡ (sym M.F.homomorphism ○ M.F.F-resp-≈ (Braided.braiding.iso.isoʳ BV _) ○ M.F.identity)) ⟩ 
      M.F.₁ B⇒ ∘ (M.F.₁ B⇐ ∘ σ ∘ B⇒) ∘ B⇐ ∎
      where 
        open HomReasoning
        open MR C
        open Equiv


  record CommutativeMonad : Set (o ⊔ ℓ ⊔ e) where
    field
      strongMonad : StrongMonad V
      commutative : Commutative strongMonad

    open StrongMonad strongMonad public
    open Commutative commutative public

