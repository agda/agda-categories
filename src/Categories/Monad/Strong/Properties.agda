{-# OPTIONS --without-K --safe #-}

-- In braided monoidal categories left and right strength imply each other

module Categories.Monad.Strong.Properties where

open import Level
open import Data.Product using (_,_; _×_)

open import Categories.Category using (Category; module Commutation)
import Categories.Category.Construction.Core as Core
open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Monoidal using (Monoidal)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
import Categories.Category.Monoidal.Utilities as MonoidalUtils
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong using (Strength; RightStrength; StrongMonad; RightStrongMonad)

import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

-- FIXME: make these top-level module parameters and remove this anonymous module?
module _ {C : Category o ℓ e} {V : Monoidal C} (BV : Braided V) where
  open Category C
  open Braided BV
  open BraidedProps BV using (braiding-coherence; inv-braiding-coherence)
  open MonoidalUtils V using (_⊗ᵢ_)
  open MonoidalUtils.Shorthands V  -- for λ⇒, ρ⇒, α⇒, ...
  open Core.Shorthands C           -- for idᵢ, _∘ᵢ_, ...
  open MonoidalReasoning V
  open MR C
  open Commutation C

  private
    variable
      X Y Z W : Obj

  module LeftStrength {M : Monad C} (leftStrength : Strength V M) where
    open BraidedProps.Shorthands BV renaming (σ to B; σ⇒ to B⇒; σ⇐ to B⇐)
    open Monad M using (F; μ; η)
    module leftStrength = Strength leftStrength

    module Shorthands where
      module σ = leftStrength.strengthen

      σ : ∀ {X Y} → X ⊗₀ F.₀ Y ⇒ F.₀ (X ⊗₀ Y)
      σ {X} {Y} = σ.η (X , Y)

    open Shorthands

    -- The left strength induces a right strength via braiding.

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

    -- The strengths commute with braiding

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

    -- Reversing a ternary product via braiding commutes with the
    -- associator.
    --
    -- FIXME: this is a lemma just about associators and braiding, so
    -- it should probably be exported to
    -- Categories.Category.Monoidal.Braided.Properties. There might
    -- also be a more straight-forward way to state and prove it.

    assoc-reverse : [ X ⊗₀ (Y ⊗₀ Z) ⇒ (X ⊗₀ Y) ⊗₀ Z ]⟨
                      id ⊗₁ B⇒      ⇒⟨ X ⊗₀ (Z ⊗₀ Y) ⟩
                      B⇒            ⇒⟨ (Z ⊗₀ Y) ⊗₀ X ⟩
                      α⇒            ⇒⟨ Z ⊗₀ (Y ⊗₀ X) ⟩
                      id ⊗₁ B⇐      ⇒⟨ Z ⊗₀ (X ⊗₀ Y) ⟩
                      B⇐
                    ≈ α⇐
                    ⟩
    assoc-reverse = begin
      B⇐ ∘ id ⊗₁ B⇐ ∘ α⇒ ∘ B⇒ ∘ id ⊗₁ B⇒    ≈˘⟨ refl⟩∘⟨ assoc²' ⟩
      B⇐ ∘ (id ⊗₁ B⇐ ∘ α⇒ ∘ B⇒) ∘ id ⊗₁ B⇒  ≈⟨ refl⟩∘⟨ pushˡ hex₁' ⟩
      B⇐ ∘ (α⇒ ∘ B⇒ ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ B⇒  ≈⟨ refl⟩∘⟨ pullʳ (sym-assoc ○ hexagon₂) ⟩
      B⇐ ∘ α⇒ ∘ (α⇐ ∘ B⇒) ∘ α⇐              ≈⟨ refl⟩∘⟨ pullˡ (cancelˡ associator.isoʳ) ⟩
      B⇐ ∘ B⇒ ∘ α⇐                          ≈⟨ cancelˡ (braiding.iso.isoˡ _) ⟩
      α⇐                                    ∎
      where
        hex₁' = conjugate-from associator (idᵢ ⊗ᵢ B) (⟺ (hexagon₁ ○ sym-assoc))

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
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ leftStrength.strength-assoc ⟩
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

  Strength⇒RightStrength : ∀ {M : Monad C} → Strength V M → RightStrength V M
  Strength⇒RightStrength {M} strength = record
    { strengthen = right-strengthen
    ; identityˡ = identityˡ'
    ; η-comm = η-comm'
    ; μ-η-comm = μ-η-comm'
    ; strength-assoc = right-strength-assoc
    }
    where
      open LeftStrength strength
      open Monad M using (F; μ; η)
      module strength = Strength strength
      module t = strength.strengthen
      B = braiding.⇒.η
      open BraidedProps.Shorthands BV using () renaming (σ⇐ to B⇐)
      τ : ∀ ((X , Y) : Obj × Obj) → F.₀ X ⊗₀ Y ⇒ F.₀ (X ⊗₀ Y)
      τ (X , Y) = F.₁ B⇐ ∘ t.η (Y , X) ∘ B (F.₀ X , Y)
      identityˡ' : ∀ {X : Obj} → F.₁ unitorʳ.from ∘ τ (X , unit) ≈ unitorʳ.from
      identityˡ' {X} = begin
        F.₁ unitorʳ.from ∘ F.₁ B⇐ ∘ t.η (unit , X) ∘ B (F.₀ X , unit)             ≈⟨ pullˡ (⟺ F.homomorphism) ⟩
        F.₁ (unitorʳ.from ∘ B⇐) ∘ t.η (unit , X) ∘ B (F.₀ X , unit)               ≈⟨ ((F.F-resp-≈ (inv-braiding-coherence)) ⟩∘⟨refl) ⟩
        F.₁ unitorˡ.from ∘ t.η (unit , X) ∘ B (F.₀ X , unit)                      ≈⟨ pullˡ strength.identityˡ ⟩
        unitorˡ.from ∘ B (F.₀ X , unit)                                           ≈⟨ braiding-coherence ⟩
        unitorʳ.from                                                              ∎
      η-comm' : ∀ {X Y : Obj} → τ (X , Y) ∘ η.η X ⊗₁ id ≈ η.η (X ⊗₀ Y)
      η-comm' {X} {Y} = begin
        (F.₁ B⇐ ∘ t.η (Y , X) ∘ B (F.₀ X , Y)) ∘ (η.η X ⊗₁ id) ≈⟨ pullʳ (pullʳ (braiding.⇒.commute (η.η X , id))) ⟩
        F.₁ B⇐ ∘ t.η (Y , X) ∘ ((id ⊗₁ η.η X) ∘ B (X , Y))     ≈⟨ (refl⟩∘⟨ (pullˡ strength.η-comm)) ⟩
        F.₁ B⇐ ∘ η.η (Y ⊗₀ X) ∘ B (X , Y)                      ≈⟨ pullˡ (⟺ (η.commute B⇐)) ⟩
        (η.η (X ⊗₀ Y) ∘ B⇐) ∘ B (X , Y)                        ≈⟨ cancelʳ (braiding.iso.isoˡ _) ⟩
        η.η (X ⊗₀ Y)                                                                          ∎
      μ-η-comm' : ∀ {X Y : Obj} → μ.η (X ⊗₀ Y) ∘ F.₁ (τ (X , Y)) ∘ τ (F.₀ X , Y) ≈ τ (X , Y) ∘ μ.η X ⊗₁ id
      μ-η-comm' {X} {Y} = begin
        μ.η (X ⊗₀ Y) ∘ F.₁ (τ (X , Y)) ∘ F.₁ B⇐ ∘ t.η (Y , F.₀ X) ∘ B (F.₀ (F.₀ X) , Y)           ≈⟨ refl⟩∘⟨ pullˡ (⟺ F.homomorphism) ⟩
        μ.η (X ⊗₀ Y) ∘ F.₁ (τ (X , Y) ∘ B⇐) ∘ t.η (Y , F.₀ X) ∘ B (F.₀ (F.₀ X) , Y)               ≈⟨ (refl⟩∘⟨ ((F.F-resp-≈ (pullʳ (cancelʳ (braiding.iso.isoʳ _)))) ⟩∘⟨refl)) ⟩
        μ.η (X ⊗₀ Y) ∘ F.₁ (F.₁ B⇐ ∘ t.η (Y , X)) ∘ t.η (Y , F.₀ X) ∘ B (F.₀ (F.₀ X) , Y)         ≈⟨ (refl⟩∘⟨ (F.homomorphism ⟩∘⟨refl)) ⟩
        μ.η (X ⊗₀ Y) ∘ (F.₁ (F.₁ B⇐) ∘ F.₁ (t.η (Y , X))) ∘ t.η (Y , F.₀ X) ∘ B (F.₀ (F.₀ X) , Y) ≈⟨ pullˡ (pullˡ (μ.commute B⇐)) ⟩
        ((F.₁ B⇐ ∘ μ.η (Y ⊗₀ X)) ∘ F.₁ (t.η (Y , X))) ∘ t.η (Y , F.₀ X) ∘ B (F.₀ (F.₀ X) , Y)     ≈⟨ (assoc² ○ (refl⟩∘⟨ ⟺ assoc²')) ⟩
        F.₁ B⇐ ∘ (μ.η (Y ⊗₀ X) ∘ F.₁ (t.η (Y , X)) ∘ t.η (Y , F.₀ X)) ∘ B ((F.₀ (F.₀ X)) , Y)     ≈⟨ refl⟩∘⟨ pushˡ strength.μ-η-comm ⟩
        F.₁ B⇐ ∘ t.η (Y , X) ∘ (id ⊗₁ μ.η X) ∘ B ((F.₀ (F.₀ X)) , Y)                              ≈˘⟨ pullʳ (pullʳ (braiding.⇒.commute (μ.η X , id))) ⟩
        τ (X , Y) ∘ μ.η X ⊗₁ id ∎

  StrongMonad⇒RightStrongMonad : StrongMonad V → RightStrongMonad V
  StrongMonad⇒RightStrongMonad SM = record { M = M ; rightStrength = Strength⇒RightStrength strength }
    where
      open StrongMonad SM

  RightStrength⇒Strength : ∀ {M : Monad C} → RightStrength V M → Strength V M
  RightStrength⇒Strength {M} rightStrength = {!   !}

  RightStrongMonad⇒StrongMonad : RightStrongMonad V → StrongMonad V
  RightStrongMonad⇒StrongMonad RSM = record { M = M ; strength = RightStrength⇒Strength rightStrength }
    where
      open RightStrongMonad RSM

