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
  open BinaryProducts products

  open CommutativeMonad CM hiding (identityˡ)
  open Monad M using (η; μ)

  open StrongProps.Left.Shorthands strength
  open StrongProps.Right.Shorthands rightStrength

  Kleisli-Monoidal : Monoidal (Kleisli M)
  Kleisli-Monoidal = record
    { ⊗ = record
      { F₀ = λ (X , Y) → X × Y
      ; F₁ = λ (f , g) → (μ.η _ ∘ M.F.₁ τ ∘ σ) ∘ (f ⁂ g)
      ; identity = λ {(A , B)} → begin 
        (μ.η _ ∘ M.F.₁ τ ∘ σ) ∘ (η.η _ ⁂ η.η _)             ≈˘⟨ refl⟩∘⟨ (⁂∘⁂ ○ ⁂-cong₂ identityˡ identityʳ) ⟩ 
        (μ.η _ ∘ M.F.₁ τ ∘ σ) ∘ (id ⁂ η.η _) ∘ (η.η _ ⁂ id) ≈⟨ pullˡ (pullʳ (pullʳ η-comm)) ⟩ 
        (μ.η _ ∘ M.F.₁ τ ∘ η.η _) ∘ (η.η _ ⁂ id)            ≈⟨ (refl⟩∘⟨ (sym (η.commute _))) ⟩∘⟨refl ⟩ 
        (μ.η _ ∘ η.η _ ∘ τ) ∘ (η.η _ ⁂ id)                  ≈⟨ (cancelˡ (Monad.identityʳ M)) ⟩∘⟨refl ⟩ 
        τ ∘ (η.η _ ⁂ id)                                    ≈⟨ RightStrength.η-comm rightStrength ⟩ 
        η.η _                                               ∎
      ; homomorphism = λ {X} {Y} {Z} {(f , g)} {(h , i)} → begin 
        (μ.η _ ∘ M.F.₁ τ ∘ σ) ∘ (((μ.η _ ∘ M.F.F₁ h) ∘ f) ⁂ ((μ.η _ ∘ M.F.F₁ i) ∘ g)) ≈˘⟨ sym assoc²βε ○ (∘-resp-≈ʳ (pullˡ ⁂∘⁂ ○ ⁂∘⁂)) ⟩ 
        μ.η _ ∘ M.F.F₁ τ ∘ σ ∘ (μ.η _ ⁂ μ.η _) ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (extendʳ (sym (Strength.strength-natural-id strength (μ.η _))) ○ ∘-resp-≈ʳ (pullˡ (⁂∘⁂ ○ ⁂-cong₂ identityʳ identityˡ))) ⟩ 
        μ.η _ ∘ M.F.F₁ τ ∘ M.F.₁ (μ.η _ ⁂ id) ∘ σ ∘ (id ⁂ μ.η _) ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ refl⟩∘⟨ (pullˡ (sym M.F.homomorphism)) ⟩ 
        μ.η _ ∘ M.F.F₁ (τ ∘ (μ.η _ ⁂ id)) ∘ σ ∘ (id ⁂ μ.η _) ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ extendʳ (assoc ○ Strength.μ-η-comm strength)) ⟩ 
        μ.η _ ∘ M.F.F₁ (τ ∘ (μ.η _ ⁂ id)) ∘ μ.η _ ∘ M.F.₁ σ ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈˘⟨ refl⟩∘⟨ (extendʳ (μ.commute _)) ⟩ 
        μ.η _ ∘ μ.η _ ∘ M.F.₁ (M.F.F₁ (τ ∘ (μ.η _ ⁂ id))) ∘ M.F.₁ σ ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym M.F.homomorphism) ⟩ 
        μ.η _ ∘ μ.η _ ∘ M.F.₁ (M.F.F₁ (τ ∘ (μ.η _ ⁂ id)) ∘ σ) ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ((M.F.F-resp-≈ (∘-resp-≈ˡ (M.F.F-resp-≈ (RightStrength.μ-η-comm rightStrength)))) ⟩∘⟨refl) ⟩ 
        μ.η _ ∘ μ.η _ ∘ M.F.₁ (M.F.F₁ (μ.η _ ∘ M.F.₁ τ ∘ τ) ∘ σ) ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ({!   !}) ⟩ 
        μ.η _ ∘ μ.η _ ∘ M.F.₁ (M.F.F₁ (μ.η _ ∘ M.F.₁ τ)) ∘ M.F.₁ (M.F.₁ τ) ∘ M.F.₁ σ ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ {!   !} ⟩
        μ.η _ ∘ M.F.F₁ (μ.η _ ∘ M.F.₁ τ) ∘ μ.η _ ∘ M.F.₁ (M.F.₁ τ) ∘ M.F.₁ σ ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ {!   !} ⟩
        μ.η _ ∘ μ.η _ ∘ M.F.₁ (M.F.₁ τ) ∘ μ.η _ ∘ M.F.₁ (M.F.₁ τ) ∘ M.F.₁ σ ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ {!   !} ⟩
        μ.η _ ∘ M.F.₁ τ ∘ μ.η _ ∘ μ.η _ ∘ M.F.₁ (M.F.₁ τ) ∘ M.F.₁ σ ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ {!   !} ⟩
        μ.η _ ∘ M.F.₁ τ ∘ μ.η _ ∘ M.F.₁ (μ.η _ ∘ M.F.₁ τ ∘ σ) ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ {!   !} ⟩
        μ.η _ ∘ M.F.₁ τ ∘ μ.η _ ∘ M.F.₁ (μ.η _ ∘ M.F.₁ σ ∘ τ) ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ {!   !} ⟩
        μ.η _ ∘ μ.η _ ∘ M.F.₁ (M.F.F₁ (μ.η _ ∘ M.F.₁ τ ∘ σ) ∘ τ) ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ {!   !} ⟩ 
        μ.η _ ∘ μ.η _ ∘ M.F.₁ (M.F.F₁ (μ.η _ ∘ M.F.₁ τ ∘ σ)) ∘ M.F.₁ τ ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ {!   !} ⟩ 
        μ.η _ ∘ M.F.F₁ (μ.η _ ∘ M.F.₁ τ ∘ σ) ∘ μ.η _ ∘ M.F.₁ τ ∘ σ ∘ (M.F.₁ h ⁂ M.F.₁ i) ∘ (f ⁂ g) ≈⟨ {!   !} ⟩ 
        μ.η _ ∘ M.F.F₁ (μ.η _ ∘ M.F.₁ τ ∘ σ) ∘ μ.η _ ∘ M.F.₁ τ ∘ M.F.₁ (M.F.₁ h ⁂ i) ∘ σ ∘ (f ⁂ g) ≈⟨ {!   !} ⟩ 
        μ.η _ ∘ M.F.F₁ (μ.η _ ∘ M.F.₁ τ ∘ σ) ∘ μ.η _ ∘ M.F.₁ (M.F.₁ (h ⁂ i)) ∘ M.F.₁ τ ∘ σ ∘ (f ⁂ g) ≈⟨ {!   !} ⟩ 
        (μ.η _ ∘ M.F.F₁ ((μ.η _ ∘ M.F.₁ τ ∘ σ) ∘ (h ⁂ i))) ∘ (μ.η _ ∘ M.F.₁ τ ∘ σ) ∘ (f ⁂ g) ∎
      ; F-resp-≈ = λ (f≈g , h≈i) → ∘-resp-≈ʳ (⁂-cong₂ f≈g h≈i)
      }
    ; unit = ⊤
    ; unitorˡ = record { from = η.η _ ∘ π₂ ; to = η.η _ ∘ ⟨ ! , id ⟩ ; iso = record 
      { isoˡ = begin 
        (μ.η _ ∘ M.F.₁ (η.η _ ∘ ⟨ ! , id ⟩)) ∘ (η.η _ ∘ π₂)       ≈⟨ (refl⟩∘⟨ M.F.homomorphism) ⟩∘⟨refl ⟩ 
        (μ.η _ ∘ M.F.₁ (η.η _) ∘ M.F.₁ ⟨ ! , id ⟩) ∘ (η.η _ ∘ π₂) ≈⟨ cancelˡ M.identityˡ ⟩∘⟨refl ⟩ 
        M.F.₁ ⟨ ! , id ⟩ ∘ η.η _ ∘ π₂                             ≈˘⟨ extendʳ (η.commute _) ⟩ 
        η.η _ ∘ ⟨ ! , id ⟩ ∘ π₂                                   ≈⟨ refl⟩∘⟨ (⟨⟩∘ ○ ⟨⟩-cong₂ (sym (!-unique (! ∘ π₂)) ○ !-unique π₁) identityˡ) ⟩ 
        η.η _ ∘ ⟨ π₁ , π₂ ⟩                                       ≈⟨ elimʳ (BinaryProducts.η products) ⟩ 
        η.η _                                                     ∎ 
      ; isoʳ = begin 
        (μ.η _ ∘ M.F.₁ (η.η _ ∘ π₂)) ∘ (η.η _ ∘ ⟨ ! , id ⟩)       ≈⟨ (refl⟩∘⟨ M.F.homomorphism) ⟩∘⟨refl ⟩ 
        (μ.η _ ∘ M.F.₁ (η.η _) ∘ M.F.₁ π₂) ∘ (η.η _ ∘ ⟨ ! , id ⟩) ≈⟨ (cancelˡ M.identityˡ ⟩∘⟨refl) ⟩ 
        M.F.₁ π₂ ∘ η.η _ ∘ ⟨ ! , id ⟩                             ≈˘⟨ extendʳ (η.commute _) ⟩ 
        η.η _ ∘ π₂ ∘ ⟨ ! , id ⟩                                   ≈⟨ elimʳ project₂ ⟩ 
        η.η _                                                     ∎ } 
      }
    ; unitorʳ = record { from = η.η _ ∘ π₁ ; to = η.η _ ∘ ⟨ id , ! ⟩ ; iso = {!   !} }
    ; associator = {!   !}
    ; unitorˡ-commute-from = {!   !}
    ; unitorˡ-commute-to = {!   !}
    ; unitorʳ-commute-from = {!   !}
    ; unitorʳ-commute-to = {!   !}
    ; assoc-commute-from = {!   !}
    ; assoc-commute-to = {!   !}
    ; triangle = {!   !}
    ; pentagon = {!   !}
    }