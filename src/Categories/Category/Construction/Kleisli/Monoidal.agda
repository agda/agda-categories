{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Kleisli.Monoidal where

open import Level

open import Categories.Category
open import Categories.Monad hiding (id)
open import Categories.Monad.Strong
open import Categories.Monad.Strong.Properties
open import Categories.Monad.Commutative
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.SymmetricMonoidal
open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.BinaryProducts
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Object.Terminal

open import Data.Product using (_,_)

import Categories.Morphism.Reasoning as MR

import Categories.Monad.Strong.Properties as StrongProps

private
  variable
    o ℓ e : Level

module _ {𝒞 : Category o ℓ e} (cartesian : Cartesian 𝒞) (CM : CommutativeMonad (Symmetric.braided (symmetric 𝒞 cartesian))) where
  open Category 𝒞
  open MR 𝒞
  open HomReasoning
  open Equiv
  open Cartesian cartesian
  open Terminal terminal
  open BinaryProducts products hiding (η)

  open CommutativeMonad CM hiding (identityˡ)
  open Monad M using (μ)
  open TripleNotation M

  open StrongProps.Left.Shorthands strength
  open StrongProps.Right.Shorthands rightStrength

  open CartesianMonoidal cartesian using (monoidal)
  open Monoidal monoidal

  Kleisli-Monoidal : Monoidal (Kleisli M)
  Kleisli-Monoidal = record
    { ⊗ = record
      { F₀ = λ (X , Y) → X × Y
      ; F₁ = λ (f , g) → ψ ∘ (f ⁂ g)
      ; identity = begin 
        (τ * ∘ σ) ∘ (η ⁂ η)             ≈˘⟨ refl⟩∘⟨ (⁂∘⁂ ○ ⁂-cong₂ identityˡ identityʳ) ⟩ 
        (τ * ∘ σ) ∘ (id ⁂ η) ∘ (η ⁂ id) ≈⟨ pullʳ (pullˡ η-comm) ⟩ 
        τ * ∘ η ∘ (η ⁂ id)              ≈⟨ pullˡ *-identityʳ ⟩ 
        τ ∘ (η ⁂ id)                    ≈⟨ RightStrength.η-comm rightStrength ⟩
        η                               ∎
      ; homomorphism = λ {X} {Y} {Z} {(f , g)} {(h , i)} → begin 
        ψ ∘ ((h * ∘ f) ⁂ (i * ∘ g))                         ≈˘⟨ refl⟩∘⟨ (pullˡ ⁂∘⁂ ○ ⁂∘⁂) ⟩ 
        ψ ∘ (μ.η _ ⁂ μ.η _) ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈˘⟨ extendʳ ψ-μ ⟩ 
        ψ * ∘ ψ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g)             ≈⟨ refl⟩∘⟨ extendʳ ψ-comm ⟩ 
        ψ * ∘ M.F.₁ (h ⁂ i) ∘ ψ ∘ (f ⁂ g)                   ≈⟨ pullˡ *∘F₁ ⟩ 
        (ψ ∘ (h ⁂ i)) * ∘ ψ ∘ (f ⁂ g)                       ∎
      ; F-resp-≈ = λ (f≈g , h≈i) → ∘-resp-≈ʳ (⁂-cong₂ f≈g h≈i)
      }
    ; unit = unit
    ; unitorˡ = record { from = η ∘ unitorˡ.from ; to = η ∘ unitorˡ.to ; iso = record 
      { isoˡ = begin 
        (η ∘ unitorˡ.to) * ∘ (η ∘ unitorˡ.from) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ unitorˡ.to) ∘ unitorˡ.from         ≈⟨ cancelʳ unitorˡ.isoˡ ⟩ 
        η                                       ∎ 
      ; isoʳ = begin 
        (η ∘ unitorˡ.from) * ∘ (η ∘ unitorˡ.to) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ unitorˡ.from) ∘ unitorˡ.to         ≈⟨ cancelʳ unitorˡ.isoʳ ⟩ 
        η                                       ∎ 
      } }
    ; unitorʳ = record { from = η ∘ unitorʳ.from ; to = η ∘ unitorʳ.to ; iso = record 
      { isoˡ = begin 
        (η ∘ unitorʳ.to) * ∘ (η ∘ unitorʳ.from) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ unitorʳ.to) ∘ unitorʳ.from         ≈⟨ cancelʳ unitorʳ.isoˡ ⟩ 
        η                                       ∎ 
      ; isoʳ = begin 
        (η ∘ unitorʳ.from) * ∘ (η ∘ unitorʳ.to) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ unitorʳ.from) ∘ unitorʳ.to         ≈⟨ cancelʳ unitorʳ.isoʳ ⟩ 
        η                                       ∎ 
      } }
    ; associator = record { from = η ∘ associator.from ; to = η ∘ associator.to ; iso = record 
      { isoˡ = begin 
        (η ∘ associator.to) * ∘ (η ∘ associator.from) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ associator.to) ∘ associator.from         ≈⟨ cancelʳ associator.isoˡ ⟩ 
        η                                       ∎ 
      ; isoʳ = begin 
        (η ∘ associator.from) * ∘ (η ∘ associator.to) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ associator.from) ∘ associator.to         ≈⟨ cancelʳ associator.isoʳ ⟩ 
        η                                       ∎ 
      } }    
    ; unitorˡ-commute-from = λ {X} {Y} {f} → begin 
      (η ∘ unitorˡ.from) * ∘ ψ ∘ (η ⁂ f)                   ≈⟨ *⇒F₁ ⟩∘⟨ ψ-σ' ⟩ 
      M.F.₁ unitorˡ.from ∘ σ ∘ (id ⁂ f)                    ≈⟨ pullˡ (Strength.identityˡ strength) ⟩ 
      unitorˡ.from ∘ (id ⁂ f)                              ≈⟨ unitorˡ-commute-from ⟩ 
      f ∘ unitorˡ.from                                     ≈˘⟨ pullˡ *-identityʳ ⟩ 
      f * ∘ η ∘ unitorˡ.from                               ∎
    ; unitorˡ-commute-to = λ {X} {Y} {f} → begin 
      (η ∘ unitorˡ.to) * ∘ f                                       ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ unitorˡ.to ∘ f                                         ≈˘⟨ refl⟩∘⟨ (cancelˡ unitorˡ.isoʳ) ⟩ 
      M.F.₁ unitorˡ.to ∘ unitorˡ.from ∘ unitorˡ.to ∘ f             ≈˘⟨ pullʳ (pullˡ (Strength.identityˡ strength)) ⟩
      (M.F.₁ unitorˡ.to ∘ M.F.₁ unitorˡ.from) ∘ σ ∘ unitorˡ.to ∘ f ≈⟨ elimˡ (sym M.F.homomorphism ○ (M.F.F-resp-≈ unitorˡ.isoˡ ○ M.F.identity)) ⟩
      σ ∘ unitorˡ.to ∘ f                                           ≈˘⟨ pullʳ (sym unitorˡ-commute-to) ⟩ 
      (σ ∘ (id ⁂ f)) ∘ unitorˡ.to                                  ≈˘⟨ ψ-σ' ⟩∘⟨refl ⟩ 
      (ψ ∘ (η ⁂ f)) ∘ unitorˡ.to                                   ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (η ⁂ f)) * ∘ η ∘ unitorˡ.to                             ∎
    ; unitorʳ-commute-from = λ {X} {Y} {f} → begin 
      (η ∘ unitorʳ.from) * ∘ ψ ∘ (f ⁂ η) ≈⟨ *⇒F₁ ⟩∘⟨ ψ-τ' ⟩ 
      M.F.₁ unitorʳ.from ∘ τ ∘ (f ⁂ id)  ≈⟨ pullˡ (RightStrength.identityˡ rightStrength) ⟩ 
      unitorʳ.from ∘ (f ⁂ id)            ≈⟨ unitorʳ-commute-from ⟩ 
      f ∘ unitorʳ.from                   ≈˘⟨ pullˡ *-identityʳ ⟩ 
      f * ∘ η ∘ unitorʳ.from             ∎
    ; unitorʳ-commute-to = λ {X} {Y} {f} → begin 
      (η ∘ unitorʳ.to) * ∘ f                                       ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ unitorʳ.to ∘ f                                         ≈˘⟨ refl⟩∘⟨ (cancelˡ unitorʳ.isoʳ) ⟩ 
      M.F.₁ unitorʳ.to ∘ unitorʳ.from ∘ unitorʳ.to ∘ f             ≈˘⟨ pullʳ (pullˡ (RightStrength.identityˡ rightStrength)) ⟩
      (M.F.₁ unitorʳ.to ∘ M.F.₁ unitorʳ.from) ∘ τ ∘ unitorʳ.to ∘ f ≈⟨ elimˡ (sym M.F.homomorphism ○ (M.F.F-resp-≈ unitorʳ.isoˡ ○ M.F.identity)) ⟩
      τ ∘ unitorʳ.to ∘ f                                           ≈˘⟨ pullʳ (sym unitorʳ-commute-to) ⟩ 
      (τ ∘ (f ⁂ id)) ∘ unitorʳ.to                                  ≈˘⟨ ψ-τ' ⟩∘⟨refl ⟩ 
      (ψ ∘ (f ⁂ η)) ∘ unitorʳ.to                                   ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (f ⁂ η)) * ∘ η ∘ unitorʳ.to                             ∎
    ; assoc-commute-from = λ {X} {Y} {f} {A} {B} {g} {U} {V} {h} → begin 
      (η ∘ associator.from) * ∘ ψ ∘ (ψ ∘ (f ⁂ g) ⁂ h) ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ associator.from ∘ ψ ∘ (ψ ∘ (f ⁂ g) ⁂ h) ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      ψ ∘ (id ⁂ ψ) ∘ associator.from ∘ ((f ⁂ g) ⁂ h) ≈˘⟨ pullʳ (pullʳ (sym assoc-commute-from)) ⟩ 
      (ψ ∘ (id ⁂ ψ) ∘ (f ⁂ (g ⁂ h))) ∘ associator.from ≈⟨ {!   !} ⟩ 
      (ψ ∘ (f ⁂ ψ ∘ (g ⁂ h))) ∘ associator.from ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (f ⁂ ψ ∘ (g ⁂ h))) * ∘ (η ∘ associator.from) ∎
    ; assoc-commute-to = {!   !}
    ; triangle = {!   !}
    ; pentagon = {!   !}
    }
