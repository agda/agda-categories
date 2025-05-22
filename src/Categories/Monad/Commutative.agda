{-# OPTIONS --without-K --allow-unsolved-metas #-}

-- Commutative Monad on a braided monoidal category
-- https://ncatlab.org/nlab/show/commutative+monad

module Categories.Monad.Commutative where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Construction.Kleisli hiding (Kleisli)
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong using (StrongMonad; RightStrength; Strength)
import Categories.Monad.Strong.Properties as StrongProps
open import Categories.Functor.Core

import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} {V : Monoidal C} (B : Braided V) where
  record Commutative (LSM : StrongMonad V) : Set (o ⊔ ℓ ⊔ e) where
    open Category C -- using (_⇒_; _∘_; _≈_)
    open Braided B using (_⊗₀_; _⊗₁_; associator)
    open StrongMonad LSM using (M; strength)
    open StrongProps.Left.Shorthands strength
    -- open Monoidal V

    rightStrength : RightStrength V M
    rightStrength = StrongProps.Strength⇒RightStrength B strength

    open StrongProps.Right.Shorthands rightStrength

    field
      commutes : ∀ {X Y} → (M.μ.η (X ⊗₀ Y) ∘ M.F.₁ τ) ∘ σ ≈ (M.μ.η (X ⊗₀ Y) ∘ M.F.₁ σ) ∘ τ

    open HomReasoning
    open Equiv
    open MR C

    ψ : ∀ {A B} → M.F.₀ A ⊗₀ M.F.₀ B ⇒ M.F.₀ (A ⊗₀ B)
    ψ = (M.μ.η _ ∘ M.F.₁ τ) ∘ σ
    ψ-comm : ∀ {A B C D} {f : A ⇒ B} {g : C ⇒ D} → ψ ∘ (M.F.₁ f ⊗₁ M.F.₁ g) ≈ M.F.₁ (f ⊗₁ g) ∘ ψ
    ψ-comm {A} {B} {C} {D} {f} {g} = begin 
      ((M.μ.η _ ∘ M.F.₁ τ) ∘ σ) ∘ (M.F.₁ f ⊗₁ M.F.₁ g) ≈⟨ pullʳ (Strength.strengthen.commute strength (M.F.F₁ f , g)) ⟩ 
      (M.μ.η _ ∘ M.F.₁ τ) ∘ M.F.₁ (M.F.₁ f ⊗₁ g) ∘ σ   ≈⟨ pullʳ (pullˡ (sym M.F.homomorphism)) ⟩ 
      M.μ.η _ ∘ M.F.₁ (τ ∘ (M.F.₁ f ⊗₁ g)) ∘ σ         ≈⟨ refl⟩∘⟨ (M.F.F-resp-≈ (RightStrength.strengthen.commute rightStrength (f , g))) ⟩∘⟨refl ⟩
      M.μ.η _ ∘ M.F.₁ (M.F.₁ (f ⊗₁ g) ∘ τ) ∘ σ         ≈˘⟨ refl⟩∘⟨ (pullˡ (sym M.F.homomorphism)) ⟩
      M.μ.η _ ∘ M.F.₁ (M.F.₁ (f ⊗₁ g)) ∘ M.F.₁ τ ∘ σ   ≈⟨ pullˡ (M.μ.commute (f ⊗₁ g)) ○ pullʳ sym-assoc ⟩
      M.F.₁ (f ⊗₁ g) ∘ ψ                               ∎
    ψ-τ : ∀ {A B} → ψ {A} {B} ∘ (id ⊗₁ M.η.η _) ≈ τ
    ψ-τ = begin 
      ((M.μ.η _ ∘ M.F.₁ τ) ∘ σ) ∘ (id ⊗₁ M.η.η _) ≈⟨ pullʳ (Strength.η-comm strength) ⟩ 
      (M.μ.η _ ∘ M.F.₁ τ) ∘ M.η.η _               ≈⟨ pullʳ (sym (M.η.commute τ)) ⟩ 
      M.μ.η _ ∘ M.η.η _ ∘ τ                       ≈⟨ cancelˡ M.identityʳ ⟩ 
      τ                                           ∎
    ψ-τ' : ∀ {A B C} {f : A ⇒ M.F.₀ B} → ψ {B} {C} ∘ (f ⊗₁ M.η.η _) ≈ τ ∘ (f ⊗₁ id)
    ψ-τ' {A} {B'} {C} {f} = begin 
      ψ ∘ (f ⊗₁ M.η.η _)              ≈˘⟨ refl⟩∘⟨ (sym (Functor.homomorphism (Braided.⊗ B)) ○ Functor.F-resp-≈ (Braided.⊗ B) (identityˡ , identityʳ)) ⟩ 
      ψ ∘ (id ⊗₁ M.η.η _) ∘ (f ⊗₁ id) ≈⟨ pullˡ ψ-τ ⟩ 
      τ ∘ (f ⊗₁ id)                   ∎

    ψ-σ : ∀ {A B} → ψ {A} {B} ∘ (M.η.η _ ⊗₁ id) ≈ σ
    ψ-σ = begin 
      ((M.μ.η _ ∘ M.F.₁ τ) ∘ σ) ∘ (M.η.η _ ⊗₁ id) ≈⟨ commutes ⟩∘⟨refl ⟩ 
      ((M.μ.η _ ∘ M.F.₁ σ) ∘ τ) ∘ (M.η.η _ ⊗₁ id) ≈⟨ pullʳ (RightStrength.η-comm rightStrength) ⟩ 
      (M.μ.η _ ∘ M.F.₁ σ) ∘ M.η.η _               ≈⟨ pullʳ (sym (M.η.commute σ)) ⟩ 
      M.μ.η _ ∘ M.η.η _ ∘ σ                       ≈⟨ cancelˡ M.identityʳ ⟩ 
      σ                                           ∎
    ψ-σ' : ∀ {A B C} {f : A ⇒ M.F.₀ B} → ψ {C} {B} ∘ (M.η.η _ ⊗₁ f) ≈ σ ∘ (id ⊗₁ f)
    ψ-σ' {A} {B'} {C} {f} = begin 
      ψ ∘ (M.η.η _ ⊗₁ f)              ≈˘⟨ refl⟩∘⟨ (sym (Functor.homomorphism (Braided.⊗ B)) ○ Functor.F-resp-≈ (Braided.⊗ B) (identityʳ , identityˡ)) ⟩ 
      ψ ∘ (M.η.η _ ⊗₁ id) ∘ (id ⊗₁ f) ≈⟨ pullˡ ψ-σ ⟩ 
      σ ∘ (id ⊗₁ f)                   ∎

    ψ-η : ∀ {A B} → ψ ∘ (M.η.η _ ⊗₁ M.η.η _) ≈ M.η.η (A ⊗₀ B)
    ψ-η = begin 
      ψ ∘ (M.η.η _ ⊗₁ M.η.η _) ≈⟨ ψ-σ' ⟩ 
      σ ∘ (id ⊗₁ M.η.η _)      ≈⟨ Strength.η-comm strength ⟩ 
      M.η.η _                  ∎
    ψ-μ : ∀ {A B} → (M.μ.η _ ∘ M.F.₁ ψ) ∘ ψ ≈ ψ {A} {B} ∘ (M.μ.η _ ⊗₁ M.μ.η _)
    ψ-μ = begin 
      (τ * ∘ σ) * ∘ τ * ∘ σ                               ≈⟨ *-assoc ⟩∘⟨refl ⟩ 
      (τ * ∘ σ *) ∘ τ * ∘ σ                               ≈⟨ pullʳ (pullˡ *-sym-assoc) ⟩ 
      τ * ∘ (σ * ∘ τ) * ∘ σ                               ≈⟨ refl⟩∘⟨ *-resp-≈ (sym commutes) ⟩∘⟨refl ⟩ 
      τ * ∘ (τ * ∘ σ) * ∘ σ                               ≈⟨ refl⟩∘⟨ *-assoc ⟩∘⟨refl ⟩ 
      τ * ∘ (τ * ∘ σ *) ∘ σ                               ≈⟨ pullˡ (pullˡ (*-sym-assoc)) ⟩ 
      ((τ * ∘ τ) * ∘ σ *) ∘ σ                             ≈⟨ *-resp-≈ (assoc ○ RightStrength.μ-η-comm rightStrength) ⟩∘⟨refl ⟩∘⟨refl ⟩ 
      ((τ ∘ (M.μ.η _ ⊗₁ id)) * ∘ σ *) ∘ σ                 ≈⟨ pullʳ (assoc ○ Strength.μ-η-comm strength) ⟩ 
      (τ ∘ (M.μ.η _ ⊗₁ id)) * ∘ σ ∘ (id ⊗₁ M.μ.η _)       ≈⟨ sym *∘F₁ ⟩∘⟨refl ⟩ 
      (τ * ∘ M.F.₁ (M.μ.η _ ⊗₁ id)) ∘ σ ∘ (id ⊗₁ M.μ.η _) ≈⟨ pullʳ (extendʳ (sym (Strength.strength-natural-id strength (M.μ.η _)))) ⟩ 
      τ * ∘ σ ∘ (M.μ.η _ ⊗₁ id) ∘ (id ⊗₁ M.μ.η _)         ≈⟨ (sym-assoc ○ ∘-resp-≈ʳ (sym (Functor.homomorphism (Braided.⊗ B)) ○ Functor.F-resp-≈ (Braided.⊗ B) (identityʳ , identityˡ))) ⟩ 
      ψ ∘ (M.μ.η _ ⊗₁ M.μ.η _)                            ∎
      where
      -- use kleisli triple notation to make the proof more readable
      open TripleNotation M 
    
    ψ-assoc-to : ∀ {A B C} → M.F.₁ associator.to ∘ ψ ∘ (id ⊗₁ ψ) ≈ ψ {A ⊗₀ B} {C} ∘ (ψ ⊗₁ id) ∘ associator.to
    ψ-assoc-to = {!   !}

    ψ-assoc-from : ∀ {A B C : Obj} → M.F.₁ associator.from ∘ ψ {A ⊗₀ B} {C} ∘ (ψ ⊗₁ id) ≈ ψ ∘ (id ⊗₁ ψ) ∘ associator.from
    ψ-assoc-from = begin 
      M.F.₁ associator.from ∘ ψ ∘ (ψ ⊗₁ id) ≈⟨ {!   !} ⟩ 
      M.μ.η _ ∘ M.F.₁ (M.F.₁ associator.from) ∘ M.F.₁ σ ∘ τ ∘ (ψ ⊗₁ id) ≈⟨ {!   !} ⟩
      M.μ.η _ ∘ M.F.₁ (M.F.₁ associator.from ∘ σ) ∘ τ ∘ (ψ ⊗₁ id) ≈⟨ refl⟩∘⟨ M.F.F-resp-≈ (Strength.strength-assoc strength) ⟩∘⟨refl ⟩
      M.μ.η _ ∘ M.F.₁ (σ ∘ (id ⊗₁ σ) ∘ associator.from) ∘ τ ∘ (ψ ⊗₁ id) ≈⟨ {!   !} ⟩
      M.μ.η _ ∘ M.F.₁ (σ ∘ (id ⊗₁ σ) ∘ associator.from) ∘ τ ∘ (M.μ.η _ ⊗₁ id) ∘ ((M.F.₁ σ ∘ τ) ⊗₁ id) ≈⟨ {!   !} ⟩
      M.μ.η _ ∘ M.F.₁ (σ ∘ (id ⊗₁ σ) ∘ associator.from) ∘ M.μ.η _ ∘ M.F.₁ τ ∘ τ ∘ ((M.F.₁ σ ∘ τ) ⊗₁ id) ≈⟨ {!   !} ⟩
      M.μ.η _ ∘ M.F.₁ (σ ∘ (id ⊗₁ σ) ∘ associator.from) ∘ M.μ.η _ ∘ M.F.₁ τ ∘ M.F.₁ (σ ⊗₁ id) ∘ τ ∘ (τ ⊗₁ id) ≈⟨ {!   !} ⟩
      M.μ.η _ ∘ M.F.₁ (σ ∘ (id ⊗₁ σ) ∘ associator.from) ∘ M.μ.η _ ∘ M.F.₁ τ ∘ M.F.₁ (σ ⊗₁ id) ∘ τ ∘ (τ ⊗₁ id) ∘ associator.to ∘ associator.from ≈⟨ {!   !} ⟩
      M.μ.η _ ∘ M.F.₁ (σ ∘ (id ⊗₁ σ) ∘ associator.from) ∘ M.μ.η _ ∘ M.F.₁ τ ∘ M.F.₁ (σ ⊗₁ id) ∘ M.F.₁ associator.to ∘ τ ∘ associator.from ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      M.μ.η _ ∘ M.F.₁ ψ ∘ M.F.₁ (id ⊗₁ τ) ∘ M.F.₁ associator.from ∘ σ ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      ψ ∘ (id ⊗₁ ψ) ∘ associator.from ∎
      where
      -- NOTE: μ ∘ M σ ∘ σ ≈ σ ∘ (id ⁂ μ)
      -- use kleisli triple notation to make the proof more readable
      open TripleNotation M 

  record CommutativeMonad : Set (o ⊔ ℓ ⊔ e) where
    field
      strongMonad : StrongMonad V
      commutative : Commutative strongMonad

    open StrongMonad strongMonad public
    open Commutative commutative public

