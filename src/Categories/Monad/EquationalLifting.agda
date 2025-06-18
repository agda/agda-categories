{-# OPTIONS --without-K --safe #-}

-- Equational Lifting Monads, as introduced in "An Equational Notion of Lifting Monad" by Bucalo et al.

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Monad.Strong using (RightStrength)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Commutative.Properties using (module CommutativeProperties)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Cartesian.SymmetricMonoidal using (symmetric)
open import Categories.Category.Construction.Kleisli using (module TripleNotation)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

import Categories.Monad.Strong.Properties as StrongProps
import Categories.Morphism.Reasoning as MR

module Categories.Monad.EquationalLifting {o ℓ e} {C : Category o ℓ e} (cartesian : Cartesian C) where
  open Category C
  open Cartesian cartesian using (products)
  open BinaryProducts products hiding (η)

  open CartesianMonoidal cartesian using (monoidal)
  open Symmetric (symmetric C cartesian) using (braided)

  record EquationalLifting (CM : CommutativeMonad braided) : Set (o ⊔ e) where
    open CommutativeMonad CM using (M; strength; rightStrength)
    open CommutativeProperties braided CM using (ψ)
    open StrongProps.Left strength using (left-right-braiding-comm; right-left-braiding-comm)
    open StrongProps.Left.Shorthands strength using (σ)
    open StrongProps.Right.Shorthands rightStrength using (τ)

    field
      lifting : ∀ {X} → σ ∘ Δ {M.F.₀ X} ≈ M.F.₁ ⟨ M.η.η X , id ⟩

    open TripleNotation M
    open HomReasoning
    open MR C
    open Equiv

    ψ-lifting : ∀ {X} → ψ ∘ Δ ≈ M.F.₁ (Δ {X})
    ψ-lifting = begin 
      (τ * ∘ σ) ∘ Δ          ≈⟨ pullʳ lifting ⟩ 
      τ * ∘ M.F.₁ ⟨ η , id ⟩ ≈⟨ *∘F₁ ⟩ 
      (τ ∘ ⟨ η , id ⟩) *     ≈⟨ *-resp-≈ (∘-resp-≈ʳ (sym ⁂∘Δ)) ⟩ 
      (τ ∘ (η ⁂ id) ∘ Δ) *   ≈⟨ *-resp-≈ (pullˡ (RightStrength.η-comm rightStrength)) ⟩ 
      (η ∘ Δ) *              ≈⟨ *⇒F₁ ⟩ 
      M.F.₁ Δ                ∎

  record EquationalLiftingMonad : Set (o ⊔ ℓ ⊔ e) where
    field
      commutativeMonad : CommutativeMonad braided
      equationalLifting : EquationalLifting commutativeMonad

    open CommutativeMonad commutativeMonad public
    open EquationalLifting equationalLifting public


