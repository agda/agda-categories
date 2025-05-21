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
        ψ * ∘ M.F.₁ (h ⁂ i) ∘ ψ ∘ (f ⁂ g)                   ≈⟨ pullˡ *-F₁ ⟩ 
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
    ; unitorˡ-commute-from = {!   !}
    ; unitorˡ-commute-to = {!   !}
    ; unitorʳ-commute-from = {!   !}
    ; unitorʳ-commute-to = {!   !}
    ; assoc-commute-from = {!   !}
    ; assoc-commute-to = {!   !}
    ; triangle = {!   !}
    ; pentagon = {!   !}
    }
    where
      commutes' : ∀ {A B} → τ * ∘ σ {M.F.₀ A} {B} ≈ σ * ∘ τ
      commutes' = assoc ○ commutes ○ sym-assoc
      ψ : ∀ {A B} → M.F.₀ A × M.F.₀ B ⇒ M.F.₀ (A × B)
      ψ = τ * ∘ σ
      ψ-comm : ∀ {A B C D} {f : A ⇒ B} {g : C ⇒ D} → ψ ∘ (M.F.₁ f ⁂ M.F.₁ g) ≈ M.F.₁ (f ⁂ g) ∘ ψ
      ψ-comm {A} {B} {C} {D} {f} {g} = begin 
        (τ * ∘ σ) ∘ (M.F.₁ f ⁂ M.F.₁ g) ≈⟨ pullʳ (strengthen.commute (M.F.F₁ f , g)) ⟩ 
        τ * ∘ M.F.₁ (M.F.₁ f ⁂ g) ∘ σ   ≈⟨ pullˡ *-F₁ ⟩ 
        (τ ∘ (M.F.₁ f ⁂ g)) * ∘ σ       ≈⟨ *-resp-≈ (RightStrength.strengthen.commute rightStrength (f , g)) ⟩∘⟨refl ⟩ 
        (M.F.₁ (f ⁂ g) ∘ τ) * ∘ σ       ≈˘⟨ pullˡ F₁-* ⟩ 
        M.F.₁ (f ⁂ g) ∘ ψ               ∎
      ψ-μ : ∀ {A B} → ψ * ∘ ψ ≈ ψ {A} {B} ∘ (μ.η _ ⁂ μ.η _)
      ψ-μ = begin 
        (τ * ∘ σ) * ∘ τ * ∘ σ                         ≈⟨ *-assoc ⟩∘⟨refl ⟩ 
        (τ * ∘ σ *) ∘ τ * ∘ σ                         ≈⟨ pullʳ (pullˡ *-sym-assoc) ⟩ 
        τ * ∘ (σ * ∘ τ) * ∘ σ                         ≈⟨ refl⟩∘⟨ *-resp-≈ (sym commutes') ⟩∘⟨refl ⟩ 
        τ * ∘ (τ * ∘ σ) * ∘ σ                         ≈⟨ refl⟩∘⟨ *-assoc ⟩∘⟨refl ⟩ 
        τ * ∘ (τ * ∘ σ *) ∘ σ                         ≈⟨ pullˡ (pullˡ (*-sym-assoc)) ⟩ 
        ((τ * ∘ τ) * ∘ σ *) ∘ σ                       ≈⟨ *-resp-≈ (assoc ○ RightStrength.μ-η-comm rightStrength) ⟩∘⟨refl ⟩∘⟨refl ⟩ 
        ((τ ∘ (μ.η _ ⁂ id)) * ∘ σ *) ∘ σ              ≈⟨ pullʳ (assoc ○ μ-η-comm) ⟩ 
        (τ ∘ (μ.η _ ⁂ id)) * ∘ σ ∘ (id ⁂ μ.η _)       ≈⟨ sym *-F₁ ⟩∘⟨refl ⟩ 
        (τ * ∘ M.F.₁ (μ.η _ ⁂ id)) ∘ σ ∘ (id ⁂ μ.η _) ≈⟨ pullʳ (extendʳ (sym (strength-natural-id (μ.η _)))) ⟩ 
        τ * ∘ σ ∘ (μ.η _ ⁂ id) ∘ (id ⁂ μ.η _)         ≈⟨ (sym-assoc ○ ∘-resp-≈ʳ (⁂∘⁂ ○ ⁂-cong₂ identityʳ identityˡ)) ⟩ 
        ψ ∘ (μ.η _ ⁂ μ.η _)                           ∎
