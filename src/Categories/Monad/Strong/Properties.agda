{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)

module Categories.Monad.Strong.Properties {o ℓ e} {C : Category o ℓ e} where

open import Level
open import Data.Product using (_,_; _×_)

import Categories.Category.Construction.Core as Core
open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Construction.Reverse
  using (Reverse-Monoidal; Reverse-Braided)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
import Categories.Category.Monoidal.Utilities as MonoidalUtils
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong using (Strength; RightStrength; StrongMonad; RightStrongMonad)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

-- A left strength is a right strength in the reversed category.

rightInReversed : {V : Monoidal C} {M : Monad C} →
                  Strength V M → RightStrength (Reverse-Monoidal V) M
rightInReversed left = record
  { strengthen     = ntHelper (record
    { η            = λ{ (X , Y) → strengthen.η (Y , X)       }
    ; commute      = λ{ (f , g) → strengthen.commute (g , f) }
    })
  ; identityˡ      = identityˡ
  ; η-comm         = η-comm
  ; μ-η-comm       = μ-η-comm
  ; strength-assoc = strength-assoc
  }
  where open Strength left

-- A right strength is a left strength in the reversed category.

leftInReversed : {V : Monoidal C} {M : Monad C} →
                 RightStrength V M → Strength (Reverse-Monoidal V) M
leftInReversed right = record
  { strengthen     = ntHelper (record
    { η            = λ{ (X , Y) → strengthen.η (Y , X)       }
    ; commute      = λ{ (f , g) → strengthen.commute (g , f) }
    })
  ; identityˡ      = identityˡ
  ; η-comm         = η-comm
  ; μ-η-comm       = μ-η-comm
  ; strength-assoc = strength-assoc
  }
  where open RightStrength right

open Category C hiding (identityˡ)
open MR C
open Commutation C

module Left {V : Monoidal C} {M : Monad C} (left : Strength V M) where
  open Category C using (identityˡ)
  open Monoidal V using (_⊗₀_)
  open MonoidalUtils V using (_⊗ᵢ_)
  open Core.Shorthands C             -- for idᵢ, _∘ᵢ_, ...
  open MonoidalUtils.Shorthands V    -- for λ⇒, ρ⇒, α⇒, ...
  open MonoidalReasoning V
  open Monad M using (F; μ; η)

  private
    module left = Strength left
    variable
      X Y Z W : Obj

  module Shorthands where
    module σ = left.strengthen

    σ : ∀ {X Y} → X ⊗₀ F.₀ Y ⇒ F.₀ (X ⊗₀ Y)
    σ {X} {Y} = σ.η (X , Y)

  open Shorthands

  -- In a braided monoidal category, a left strength induces a right strength.

  module _ (BV : Braided V) where
    open Braided BV hiding (_⊗₀_)
    open BraidedProps BV using (braiding-coherence; inv-braiding-coherence; assoc-reverse)
    open BraidedProps.Shorthands BV renaming (σ to B; σ⇒ to B⇒; σ⇐ to B⇐)

    private
      τ : ∀ {X Y} → F.₀ X ⊗₀ Y ⇒ F.₀ (X ⊗₀ Y)
      τ {X} {Y} = F.₁ B⇐ ∘ σ ∘ B⇒

      τ-commute : (f : X ⇒ Z) (g : Y ⇒ W) → τ ∘ (F.₁ f ⊗₁ g) ≈ F.₁ (f ⊗₁ g) ∘ τ
      τ-commute f g = begin
        (F.₁ B⇐ ∘ σ ∘ B⇒) ∘ (F.₁ f ⊗₁ g)   ≈⟨ pullʳ (pullʳ (braiding.⇒.commute (F.₁ f , g))) ⟩
        F.₁ B⇐ ∘ σ ∘ ((g ⊗₁ F.₁ f) ∘ B⇒)   ≈⟨ refl⟩∘⟨ pullˡ (σ.commute (g , f)) ⟩
        F.₁ B⇐ ∘ (F.₁ (g ⊗₁ f) ∘ σ) ∘ B⇒   ≈˘⟨ pushˡ (pushˡ (F.homomorphism)) ⟩
        (F.₁ (B⇐ ∘ (g ⊗₁ f)) ∘ σ) ∘ B⇒     ≈⟨ pushˡ (F.F-resp-≈ (braiding.⇐.commute (f , g)) ⟩∘⟨refl) ⟩
        F.₁ ((f ⊗₁ g) ∘ B⇐) ∘ σ ∘ B⇒       ≈⟨ pushˡ F.homomorphism ⟩
        F.₁ (f ⊗₁ g) ∘ F.₁ B⇐ ∘ σ ∘ B⇒     ∎

    right-strengthen : NaturalTransformation (⊗ ∘F (F ⁂ idF)) (F ∘F ⊗)
    right-strengthen = ntHelper (record
      { η = λ _ → τ
      ; commute = λ (f , g) → τ-commute f g
      })

    private module τ = NaturalTransformation right-strengthen

    -- The strengths commute with braiding.

    left-right-braiding-comm : ∀ {X Y} → F.₁ B⇐ ∘ σ {X} {Y} ≈ τ ∘ B⇐
    left-right-braiding-comm = begin
      F.₁ B⇐ ∘ σ               ≈˘⟨ pullʳ (cancelʳ (braiding.iso.isoʳ _)) ⟩
      (F.₁ B⇐ ∘ σ ∘ B⇒) ∘ B⇐   ∎

    right-left-braiding-comm : ∀ {X Y} → F.₁ B⇒ ∘ τ {X} {Y} ≈ σ ∘ B⇒
    right-left-braiding-comm = begin
      F.₁ B⇒ ∘ (F.₁ B⇐ ∘ σ ∘ B⇒)   ≈˘⟨ pushˡ F.homomorphism ⟩
      F.₁ (B⇒ ∘ B⇐) ∘ σ ∘ B⇒       ≈⟨ F.F-resp-≈ (braiding.iso.isoʳ _) ⟩∘⟨refl ⟩
      F.₁ id ∘ σ ∘ B⇒              ≈⟨ elimˡ F.identity ⟩
      σ ∘ B⇒                       ∎

    right-identityˡ : ∀ {X} → F.₁ ρ⇒ ∘ τ {X} {unit} ≈ ρ⇒
    right-identityˡ = begin
      F.₁ ρ⇒ ∘ F.₁ B⇐ ∘ σ ∘ B⇒  ≈⟨ pullˡ (⟺ F.homomorphism) ⟩
      F.₁ (ρ⇒ ∘ B⇐) ∘ σ ∘ B⇒    ≈⟨ F.F-resp-≈ (inv-braiding-coherence) ⟩∘⟨refl ⟩
      F.₁ λ⇒ ∘ σ ∘ B⇒           ≈⟨ pullˡ left.identityˡ ⟩
      λ⇒ ∘ B⇒                   ≈⟨ braiding-coherence ⟩
      ρ⇒                        ∎

    -- The induced right strength commutes with the monad unit.

    right-η-comm : ∀ {X Y} → τ ∘ η.η X ⊗₁ id ≈ η.η (X ⊗₀ Y)
    right-η-comm {X} {Y} = begin
      (F.₁ B⇐ ∘ σ ∘ B⇒) ∘ (η.η X ⊗₁ id)  ≈⟨ pullʳ (pullʳ (braiding.⇒.commute (η.η X , id))) ⟩
      F.₁ B⇐ ∘ σ ∘ (id ⊗₁ η.η X) ∘ B⇒  ≈⟨ refl⟩∘⟨ pullˡ left.η-comm ⟩
      F.₁ B⇐ ∘ η.η (Y ⊗₀ X) ∘ B⇒       ≈⟨ pullˡ (⟺ (η.commute B⇐)) ⟩
      (η.η (X ⊗₀ Y) ∘ B⇐) ∘ B⇒         ≈⟨ cancelʳ (braiding.iso.isoˡ _) ⟩
      η.η (X ⊗₀ Y)                     ∎

    -- The induced right strength commutes with the monad multiplication.

    right-μ-η-comm : ∀ {X Y} → μ.η (X ⊗₀ Y) ∘ F.₁ τ ∘ τ ≈ τ ∘ μ.η X ⊗₁ id
    right-μ-η-comm {X} {Y} = begin
      μ.η (X ⊗₀ Y) ∘ F.₁ τ ∘ F.₁ B⇐ ∘ σ ∘ B⇒           ≈⟨ refl⟩∘⟨ pullˡ (⟺ F.homomorphism) ⟩
      μ.η (X ⊗₀ Y) ∘ F.₁ (τ ∘ B⇐) ∘ σ ∘ B⇒             ≈⟨ refl⟩∘⟨ (F.F-resp-≈ (pullʳ (cancelʳ (braiding.iso.isoʳ _))) ⟩∘⟨refl) ⟩
      μ.η (X ⊗₀ Y) ∘ F.₁ (F.₁ B⇐ ∘ σ) ∘ σ ∘ B⇒         ≈⟨ refl⟩∘⟨ F.homomorphism ⟩∘⟨refl ⟩
      μ.η (X ⊗₀ Y) ∘ (F.₁ (F.₁ B⇐) ∘ F.₁ σ) ∘ σ ∘ B⇒   ≈⟨ pullˡ (pullˡ (μ.commute B⇐)) ⟩
      ((F.₁ B⇐ ∘ μ.η (Y ⊗₀ X)) ∘ F.₁ σ) ∘ σ ∘ B⇒       ≈⟨ assoc² ○ (refl⟩∘⟨ ⟺ assoc²') ⟩
      F.₁ B⇐ ∘ (μ.η (Y ⊗₀ X) ∘ F.₁ σ ∘ σ) ∘ B⇒         ≈⟨ refl⟩∘⟨ pushˡ left.μ-η-comm ⟩
      F.₁ B⇐ ∘ σ ∘ (id ⊗₁ μ.η X) ∘ B⇒                  ≈˘⟨ pullʳ (pullʳ (braiding.⇒.commute (μ.η X , id))) ⟩
      τ ∘ μ.η X ⊗₁ id ∎

    -- The induced right strength commutes with the associator

    right-strength-assoc : [ F.₀ X ⊗₀ (Y ⊗₀ Z)  ⇒  F.₀ ((X ⊗₀ Y) ⊗₀ Z) ]⟨
                             τ                  ⇒⟨ F.₀ (X ⊗₀ (Y ⊗₀ Z)) ⟩
                             F.₁ α⇐
                           ≈ α⇐                 ⇒⟨ (F.₀ X ⊗₀ Y) ⊗₀ Z ⟩
                             τ ⊗₁ id            ⇒⟨ F.₀ (X ⊗₀ Y) ⊗₀ Z ⟩
                             τ
                           ⟩
    right-strength-assoc = begin
        F.₁ α⇐ ∘ τ
      ≈˘⟨ F.F-resp-≈ assoc-reverse ⟩∘⟨refl ⟩
        F.₁ (B⇐ ∘ id ⊗₁ B⇐ ∘ α⇒ ∘ B⇒ ∘ id ⊗₁ B⇒) ∘ τ
      ≈⟨ pushˡ F.homomorphism ⟩
        F.₁ B⇐ ∘ F.₁ (id ⊗₁ B⇐ ∘ α⇒ ∘ B⇒ ∘ id ⊗₁ B⇒) ∘ τ
      ≈⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
        F.₁ B⇐ ∘ F.₁ (id ⊗₁ B⇐) ∘ F.₁ (α⇒ ∘ B⇒ ∘ id ⊗₁ B⇒) ∘ τ
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
        F.₁ B⇐ ∘ F.₁ (id ⊗₁ B⇐) ∘ F.₁ α⇒ ∘ F.₁ (B⇒ ∘ id ⊗₁ B⇒) ∘ τ
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
        F.₁ B⇐ ∘ F.₁ (id ⊗₁ B⇐) ∘ F.₁ α⇒ ∘ F.₁ B⇒ ∘ F.₁ (id ⊗₁ B⇒) ∘ τ
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ τ.commute (id , B⇒) ⟩
        F.₁ B⇐ ∘ F.₁ (id ⊗₁ B⇐) ∘ F.₁ α⇒ ∘ F.₁ B⇒ ∘ τ ∘ F.₁ id ⊗₁ B⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ right-left-braiding-comm ⟩
        F.₁ B⇐ ∘ F.₁ (id ⊗₁ B⇐) ∘ F.₁ α⇒ ∘ σ ∘ B⇒ ∘ F.₁ id ⊗₁ B⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ left.strength-assoc ⟩
        F.₁ B⇐ ∘ F.₁ (id ⊗₁ B⇐) ∘ σ ∘ (id ⊗₁ σ ∘ α⇒) ∘ B⇒ ∘ F.₁ id ⊗₁ B⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullʳ (refl⟩∘⟨ refl⟩∘⟨ F.identity ⟩⊗⟨refl) ⟩
        F.₁ B⇐ ∘ F.₁ (id ⊗₁ B⇐) ∘ σ ∘ id ⊗₁ σ ∘ α⇒ ∘ B⇒ ∘ id ⊗₁ B⇒
      ≈˘⟨ refl⟩∘⟨ extendʳ (σ.commute (id , B⇐)) ⟩
        F.₁ B⇐ ∘ σ ∘ id ⊗₁ F.₁ B⇐ ∘ id ⊗₁ σ ∘ α⇒ ∘ B⇒ ∘ id ⊗₁ B⇒
      ≈⟨ extendʳ left-right-braiding-comm ⟩
        τ ∘ B⇐ ∘ id ⊗₁ F.₁ B⇐ ∘ id ⊗₁ σ ∘ α⇒ ∘ B⇒ ∘ id ⊗₁ B⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (parallel Equiv.refl left-right-braiding-comm) ⟩
        τ ∘ B⇐ ∘ id ⊗₁ τ ∘ id ⊗₁ B⇐ ∘ α⇒ ∘ B⇒ ∘ id ⊗₁ B⇒
      ≈⟨ refl⟩∘⟨ extendʳ (braiding.⇐.commute (τ , id)) ⟩
        τ ∘ τ ⊗₁ id ∘ B⇐ ∘ id ⊗₁ B⇐ ∘ α⇒ ∘ B⇒ ∘ id ⊗₁ B⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Equiv.refl ⟩∘⟨ (refl⟩⊗⟨ Equiv.refl) ⟩∘⟨refl ⟩
        τ ∘ τ ⊗₁ id ∘ B⇐ ∘ id ⊗₁ B⇐ ∘ α⇒ ∘ B⇒ ∘ id ⊗₁ B⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-reverse ⟩
        τ ∘ τ ⊗₁ id ∘ α⇐
      ∎

    -- The induced right strength

    right : RightStrength V M
    right = record
      { strengthen     = right-strengthen
      ; identityˡ      = right-identityˡ
      ; η-comm         = right-η-comm
      ; μ-η-comm       = right-μ-η-comm
      ; strength-assoc = right-strength-assoc
      }

Strength⇒RightStrength : {V : Monoidal C} {M : Monad C} →
                         Braided V → Strength V M → RightStrength V M
Strength⇒RightStrength BV left = Left.right left BV

StrongMonad⇒RightStrongMonad : {V : Monoidal C} →
                               Braided V → StrongMonad V → RightStrongMonad V
StrongMonad⇒RightStrongMonad BV SM = record
  { M             = M
  ; rightStrength = Strength⇒RightStrength BV strength
  }
  where open StrongMonad SM

module Right {V : Monoidal C} {M : Monad C} (right : RightStrength V M) where
  open Monoidal V using (_⊗₀_)
  open Monad M using (F)

  module Shorthands where
    module τ = RightStrength.strengthen right

    τ : ∀ {X Y} → F.₀ X ⊗₀ Y ⇒ F.₀ (X ⊗₀ Y)
    τ {X} {Y} = τ.η (X , Y)

-- In a braided monoidal category, a right strength induces a left strength.

RightStrength⇒Strength : {V : Monoidal C} {M : Monad C} →
                         Braided V → RightStrength V M → Strength V M
RightStrength⇒Strength {V} {M} BV right = record
  { strengthen     = strengthen
  ; identityˡ      = identityˡ
  ; η-comm         = η-comm
  ; μ-η-comm       = μ-η-comm
  ; strength-assoc = strength-assoc
  }
  where
    left₁ : Strength (Reverse-Monoidal V) M
    left₁ = leftInReversed right

    right₂ : RightStrength (Reverse-Monoidal V) M
    right₂ = Strength⇒RightStrength (Reverse-Braided BV) left₁

    -- Note: this is almost what we need, but Reverse-Monoidal is
    -- not a strict involution (some of the coherence laws are
    -- have proofs that are not strictly identical to their
    -- original counterparts). But this does not matter
    -- structurally, so we can just re-package the components we
    -- need.
    left₂ : Strength (Reverse-Monoidal (Reverse-Monoidal V)) M
    left₂ = leftInReversed right₂

    open Strength left₂

RightStrongMonad⇒StrongMonad : {V : Monoidal C} →
                               Braided V → RightStrongMonad V → StrongMonad V
RightStrongMonad⇒StrongMonad BV RSM = record
  { M        = M
  ; strength = RightStrength⇒Strength BV rightStrength
  }
  where open RightStrongMonad RSM
