{-# OPTIONS --without-K --safe #-}

-- Commutative Monad on a braided monoidal category
-- https://ncatlab.org/nlab/show/commutative+monad

module Categories.Monad.Commutative.Properties where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Construction.Kleisli hiding (Kleisli)
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong using (StrongMonad; RightStrength; Strength)
open import Categories.Monad.Commutative
import Categories.Monad.Strong.Properties as StrongProps
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Symmetric.Properties as SymmetricProps
open import Categories.Functor.Core

import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

module CommutativeProperties {C : Category o ℓ e} {V : Monoidal C} (BV : Braided V) (CM : CommutativeMonad BV) where
  open Category C -- using (_⇒_; _∘_; _≈_)
  open Braided BV using (_⊗₀_; _⊗₁_; associator)
  open CommutativeMonad CM hiding (identityˡ)
  -- open StrongMonad LSM using (M; strength)
  open StrongProps.Left.Shorthands strength
  -- open Monoidal V

  -- rightStrength : RightStrength V M
  -- rightStrength = StrongProps.Strength⇒RightStrength BV strength

  open StrongProps.Right.Shorthands rightStrength

  open HomReasoning
  open Equiv
  open MR C

  private
    module ⊗ = Functor (Braided.⊗ BV)

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
    ψ ∘ (f ⊗₁ M.η.η _)              ≈˘⟨ refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) ⟩ 
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
    ψ ∘ (M.η.η _ ⊗₁ f)              ≈˘⟨ refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , identityˡ)) ⟩ 
    ψ ∘ (M.η.η _ ⊗₁ id) ∘ (id ⊗₁ f) ≈⟨ pullˡ ψ-σ ⟩ 
    σ ∘ (id ⊗₁ f)                   ∎

  ψ-η : ∀ {A B} → ψ ∘ (M.η.η _ ⊗₁ M.η.η _) ≈ M.η.η (A ⊗₀ B)
  ψ-η = begin 
    ψ ∘ (M.η.η _ ⊗₁ M.η.η _) ≈⟨ ψ-σ' ⟩ 
    σ ∘ (id ⊗₁ M.η.η _)      ≈⟨ Strength.η-comm strength ⟩ 
    M.η.η _                  ∎

  ψ-μ : ∀ {X Y} → (M.μ.η _ ∘ M.F.₁ ψ) ∘ ψ ≈ ψ {X} {Y} ∘ (M.μ.η _ ⊗₁ M.μ.η _)
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
    τ * ∘ σ ∘ (M.μ.η _ ⊗₁ id) ∘ (id ⊗₁ M.μ.η _)         ≈⟨ sym-assoc ○ ∘-resp-≈ʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , identityˡ)) ⟩ 
    ψ ∘ (M.μ.η _ ⊗₁ M.μ.η _)                            ∎
    where open TripleNotation M

  -- Extra properties if C is symmetric
module SymmetricProperties  {C : Category o ℓ e} {V : Monoidal C} (symmetric : Symmetric V) (CM : CommutativeMonad (Symmetric.braided symmetric)) where
  open Category C -- using (_⇒_; _∘_; _≈_)
  open Symmetric symmetric using (commutative) renaming (braided to BV)
  open SymmetricProps symmetric
  open BraidedProps.Shorthands BV renaming (σ to B; σ⇒ to B⇒; σ⇐ to B⇐)
  open Braided (Symmetric.braided symmetric) using (_⊗₀_; _⊗₁_; associator)
  open CommutativeMonad CM hiding (identityˡ; commutative)
  open StrongProps.Left.Shorthands strength
  open StrongProps.Left strength using (left-right-braiding-comm)
  open StrongProps.Right.Shorthands rightStrength

  open HomReasoning
  open Equiv
  open MR C
  open CommutativeProperties BV CM

  module ⊗ = Functor (Braided.⊗ BV)

  -- use kleisli triple notation to make the proof more readable
  open TripleNotation M

  private
    σ-strength-assoc' : ∀ {X Y Z} → M.F.₁ associator.to ∘ σ ∘ (id ⊗₁ σ) ≈ σ ∘ associator.to {X} {Y} {M.F.₀ Z}
    σ-strength-assoc' = begin 
      M.F.₁ associator.to ∘ σ ∘ (id ⊗₁ σ) 
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ elimʳ associator.isoʳ ⟩ 
      M.F.₁ associator.to ∘ σ ∘ (id ⊗₁ σ) ∘ associator.from ∘ associator.to 
        ≈˘⟨ refl⟩∘⟨ (pullˡ strength-assoc ○ assoc²βε) ⟩ 
      M.F.₁ associator.to ∘ M.F.₁ associator.from ∘ σ ∘ associator.to ≈⟨ cancelˡ (sym M.F.homomorphism ○ M.F.F-resp-≈ associator.isoˡ ○ M.F.identity) ⟩ 
      σ ∘ associator.to 
        ∎
    τ-strength-assoc' : ∀ {X Y Z} → M.F.₁ associator.from ∘ τ ∘ (τ ⊗₁ id) ≈ τ ∘ associator.from {M.F.₀ X} {Y} {Z}
    τ-strength-assoc' = begin 
      M.F.₁ associator.from ∘ τ ∘ (τ ⊗₁ id) 
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ elimʳ associator.isoˡ ⟩ 
      M.F.₁ associator.from ∘ τ ∘ (τ ⊗₁ id) ∘ associator.to ∘ associator.from 
        ≈˘⟨ refl⟩∘⟨ (pullˡ (RightStrength.strength-assoc rightStrength) ○ assoc²βε) ⟩ 
      M.F.₁ associator.from ∘ M.F.₁ associator.to ∘ τ ∘ associator.from ≈⟨ cancelˡ (sym M.F.homomorphism ○ M.F.F-resp-≈ associator.isoʳ ○ M.F.identity) ⟩ 
      τ ∘ associator.from 
        ∎
    hexagon₁' : ∀ {X Y Z} → M.F.₁ associator.to ∘ M.F.₁ (id ⊗₁ B⇐) ≈ M.F.₁ (B⇐ ⊗₁ id) ∘ M.F.₁ associator.to ∘ M.F.₁ B⇒ ∘ M.F.₁ (associator.to {X} {Y} {Z})
    hexagon₁' = begin 
      M.F.₁ associator.to ∘ M.F.₁ (id ⊗₁ B⇐)                                  
        ≈⟨ sym M.F.homomorphism ⟩ 
      M.F.₁ (associator.to ∘ (id ⊗₁ B⇐))                                      
        ≈⟨ M.F.F-resp-≈ (∘-resp-≈ʳ (⊗.F-resp-≈ (refl , braiding-selfInverse))) ⟩ 
      M.F.₁ (associator.to ∘ (id ⊗₁ B⇒))                                      
        ≈˘⟨ M.F.F-resp-≈ (pullˡ (cancelˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((∘-resp-≈ˡ braiding-selfInverse ○ commutative) , identity²) ○ ⊗.identity))) ⟩ 
      M.F.₁ ((B⇐ ⊗₁ id) ∘ ((B⇒ ⊗₁ id) ∘ associator.to) ∘ (id ⊗₁ B⇒))          
        ≈⟨ M.F.F-resp-≈ (∘-resp-≈ʳ (Braided.hexagon₂ BV)) ⟩ 
      M.F.₁ ((B⇐ ⊗₁ id) ∘ (associator.to ∘ B⇒) ∘ associator.to)               
        ≈˘⟨ ∘-resp-≈ʳ (pullˡ (sym M.F.homomorphism)) ○ (∘-resp-≈ʳ (sym M.F.homomorphism) ○ sym M.F.homomorphism) ⟩  
      M.F.₁ (B⇐ ⊗₁ id) ∘ M.F.₁ associator.to ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.to 
        ∎
    hexagon₂' : ∀ {X Y Z} → M.F.₁ associator.from ∘ M.F.₁ (B⇐ ⊗₁ id) ≈ M.F.₁ (id ⊗₁ B⇐) ∘ M.F.₁ associator.from ∘ M.F.₁ B⇒ ∘ M.F.₁ (associator.from {X} {Y} {Z})
    hexagon₂' = begin 
      M.F.₁ associator.from ∘ M.F.₁ (B⇐ ⊗₁ id)                         
        ≈⟨ sym M.F.homomorphism ⟩ 
      M.F.₁ (associator.from ∘ (B⇐ ⊗₁ id))                             
        ≈⟨ M.F.F-resp-≈ (∘-resp-≈ʳ (⊗.F-resp-≈ (braiding-selfInverse , refl))) ⟩
      M.F.₁ (associator.from ∘ (B⇒ ⊗₁ id)) 
        ≈˘⟨ M.F.F-resp-≈ (pullˡ (cancelˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identity² , (∘-resp-≈ˡ braiding-selfInverse ○ commutative)) ○ ⊗.identity))) ⟩
      M.F.₁ ((id ⊗₁ B⇐) ∘ ((id ⊗₁ B⇒) ∘ associator.from) ∘ (B⇒ ⊗₁ id)) 
        ≈⟨ M.F.F-resp-≈ (∘-resp-≈ʳ (assoc ○ (Braided.hexagon₁ BV) ○ sym-assoc)) ⟩
      M.F.₁ ((id ⊗₁ B⇐) ∘ (associator.from ∘ B⇒) ∘ associator.from)    
        ≈˘⟨ ∘-resp-≈ʳ (pullˡ (sym M.F.homomorphism)) ○ (∘-resp-≈ʳ (sym M.F.homomorphism) ○ sym M.F.homomorphism) ⟩
      M.F.₁ (id ⊗₁ B⇐) ∘ M.F.₁ associator.from ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.from 
        ∎

  τ-σ-assoc-from : ∀ {X Y Z} → M.F.₁ associator.from ∘ (τ {_} {Z}) * ∘ M.F.₁ (σ {X} {Y} ⊗₁ id) ≈ σ * ∘ M.F.₁ (id ⊗₁ τ) ∘ M.F.₁ associator.from
  τ-σ-assoc-from = begin 
    M.F.₁ associator.from ∘ τ * ∘ M.F.₁ (σ ⊗₁ id) 
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ (sym M.F.homomorphism ○ M.F.F-resp-≈ (sym ⊗.homomorphism)) ○ (sym M.F.homomorphism ○ M.F.F-resp-≈ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((∘-resp-≈ˡ (cancelˡ (sym M.F.homomorphism ○ M.F.F-resp-≈ inv-commutative ○ M.F.identity)) ○ cancelʳ commutative) , elimˡ identity²)))) ⟩ 
    M.F.₁ associator.from ∘ τ * ∘ M.F.₁ (M.F.₁ B⇐ ⊗₁ id) ∘ M.F.₁ (τ ⊗₁ id) ∘ M.F.₁ (B⇒ ⊗₁ id) 
      ≈⟨ refl⟩∘⟨ extendʳ ((*∘F₁ ○ *-resp-≈ (τ.commute _)) ○ sym F₁∘*) ⟩ 
    M.F.₁ associator.from ∘ M.F.₁ (B⇐ ⊗₁ id) ∘ τ * ∘ M.F.₁ (τ ⊗₁ id) ∘ M.F.₁ (B⇒ ⊗₁ id) 
      ≈⟨ extendʳ hexagon₂' ○ ∘-resp-≈ʳ assoc²βε ⟩ 
    M.F.₁ (id ⊗₁ B⇐) ∘ M.F.₁ associator.from ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.from ∘ τ * ∘ M.F.₁ (τ ⊗₁ id) ∘ M.F.₁ (B⇒ ⊗₁ id) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ F₁∘* ○ (pullˡ (*∘F₁ ○ *-resp-≈ (assoc ○ τ-strength-assoc')) ○ sym (pullˡ *∘F₁))) ⟩ 
    M.F.₁ (id ⊗₁ B⇐) ∘ M.F.₁ associator.from ∘ M.F.₁ B⇒ ∘ τ * ∘ M.F.₁ associator.from ∘ M.F.₁ (B⇒ ⊗₁ id) 
      ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ extendʳ (F₁∘* ○ *-resp-≈ (∘-resp-≈ˡ (M.F.F-resp-≈ (sym braiding-selfInverse)) ○ cancelˡ (sym M.F.homomorphism ○ M.F.F-resp-≈ inv-commutative ○ M.F.identity)) ○ sym *∘F₁)) ⟩ 
    M.F.₁ (id ⊗₁ B⇐) ∘ M.F.₁ associator.from ∘ σ * ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.from ∘ M.F.₁ (B⇒ ⊗₁ id) 
      ≈⟨ refl⟩∘⟨ (pullˡ (F₁∘* ○ *-resp-≈ strength-assoc) ○ sym (pullˡ *∘F₁ ○ pullˡ (*∘F₁ ○ *-resp-≈ assoc))) ⟩ 
    M.F.₁ (id ⊗₁ B⇐) ∘ σ * ∘ M.F.₁ (id ⊗₁ σ) ∘ M.F.₁ associator.from ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.from ∘ M.F.₁ (B⇒ ⊗₁ id) 
      ≈⟨ extendʳ (F₁∘* ○ *-resp-≈ (sym (σ.commute _)) ○ sym *∘F₁) ⟩ 
    σ * ∘ M.F.₁ (id ⊗₁ M.F.₁ B⇐) ∘ M.F.₁ (id ⊗₁ σ) ∘ M.F.₁ associator.from ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.from ∘ M.F.₁ (B⇒ ⊗₁ id) 
      ≈⟨ (refl⟩∘⟨ extendʳ (sym M.F.homomorphism ○ M.F.F-resp-≈ (sym ⊗.homomorphism) ○ M.F.F-resp-≈ (⊗.F-resp-≈ (identity² , left-right-braiding-comm BV)) ○ sym (sym M.F.homomorphism ○ M.F.F-resp-≈ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identity² , refl))))) ⟩ 
    σ * ∘ M.F.₁ (id ⊗₁ τ) ∘ M.F.₁ (id ⊗₁ B⇐) ∘ M.F.₁ associator.from ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.from ∘ M.F.₁ (B⇒ ⊗₁ id) 
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ((pullˡ hexagon₂') ○ pullʳ assoc²βε) ⟩ 
    σ * ∘ M.F.₁ (id ⊗₁ τ) ∘ M.F.₁ associator.from ∘ M.F.₁ (B⇐ ⊗₁ id) ∘ M.F.₁ (B⇒ ⊗₁ id) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimʳ (sym M.F.homomorphism ○ M.F.F-resp-≈ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((∘-resp-≈ˡ braiding-selfInverse ○ commutative) , identity²) ○ ⊗.identity) ○ M.F.identity) ⟩ 
    σ * ∘ M.F.₁ (id ⊗₁ τ) ∘ M.F.₁ associator.from 
      ∎

  σ-τ-assoc-to : ∀ {X Y Z} → M.F.₁ associator.to ∘ (σ {X}) * ∘ M.F.₁ (id ⊗₁ τ {Y} {Z}) ≈ τ * ∘ M.F.₁ (σ ⊗₁ id) ∘ M.F.₁ associator.to
  σ-τ-assoc-to = begin
    M.F.₁ associator.to ∘ σ * ∘ M.F.₁ (id ⊗₁ τ) 
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ (sym M.F.homomorphism ○ M.F.F-resp-≈ (sym ⊗.homomorphism)) ○ (sym M.F.homomorphism ○ M.F.F-resp-≈ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (elimˡ identity² , assoc)))) ⟩ 
    M.F.₁ associator.to ∘ σ * ∘ M.F.₁ (id ⊗₁ M.F.₁ B⇐) ∘ M.F.₁ (id ⊗₁ σ) ∘ M.F.₁ (id ⊗₁ B⇒) 
      ≈⟨ refl⟩∘⟨ extendʳ ((*∘F₁ ○ *-resp-≈ (σ.commute (id , B⇐))) ○ sym F₁∘*) ⟩ 
    M.F.₁ associator.to ∘ M.F.₁ (id ⊗₁ B⇐) ∘ σ * ∘ M.F.₁ (id ⊗₁ σ) ∘ M.F.₁ (id ⊗₁ B⇒) 
      ≈⟨ extendʳ hexagon₁' ○ ∘-resp-≈ʳ assoc²βε ⟩ 
    M.F.₁ (B⇐ ⊗₁ id) ∘ M.F.₁ associator.to ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.to ∘ σ * ∘ M.F.₁ (id ⊗₁ σ) ∘ M.F.₁ (id ⊗₁ B⇒) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ F₁∘* ○ (pullˡ (*∘F₁ ○ *-resp-≈ (assoc ○ σ-strength-assoc')) ○ sym (pullˡ *∘F₁))) ⟩ 
    M.F.₁ (B⇐ ⊗₁ id) ∘ M.F.₁ associator.to ∘ M.F.₁ B⇒ ∘ σ * ∘ M.F.₁ associator.to ∘ M.F.₁ (id ⊗₁ B⇒) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (F₁∘* ○ *-resp-≈ (∘-resp-≈ˡ (M.F.F-resp-≈ (sym braiding-selfInverse)) ○ left-right-braiding-comm BV) ○ sym *∘F₁ ○ ∘-resp-≈ʳ (M.F.F-resp-≈ braiding-selfInverse)) ⟩ 
    M.F.₁ (B⇐ ⊗₁ id) ∘ M.F.₁ associator.to ∘ τ * ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.to ∘ M.F.₁ (id ⊗₁ B⇒) 
      ≈⟨ refl⟩∘⟨ (pullˡ (F₁∘* ○ *-resp-≈ (RightStrength.strength-assoc rightStrength)) ○ sym (pullˡ *∘F₁ ○ pullˡ (*∘F₁ ○ *-resp-≈ assoc))) ⟩ 
    M.F.₁ (B⇐ ⊗₁ id) ∘ τ * ∘ M.F.₁ (τ ⊗₁ id) ∘ M.F.₁ associator.to ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.to ∘ M.F.₁ (id ⊗₁ B⇒) 
      ≈⟨ extendʳ (F₁∘* ○ *-resp-≈ (sym (τ.commute _)) ○ sym *∘F₁) ⟩ 
    τ * ∘ M.F.₁ (M.F.₁ B⇐ ⊗₁ id) ∘ M.F.₁ (τ ⊗₁ id) ∘ M.F.₁ associator.to ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.to ∘ M.F.₁ (id ⊗₁ B⇒) 
      ≈⟨ refl⟩∘⟨ extendʳ (sym M.F.homomorphism ○ M.F.F-resp-≈ (sym ⊗.homomorphism) ○ M.F.F-resp-≈ (⊗.F-resp-≈ ((cancelˡ (sym M.F.homomorphism ○ M.F.F-resp-≈ inv-commutative ○ M.F.identity)) , identity²)) ○ sym (sym M.F.homomorphism ○ M.F.F-resp-≈ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((∘-resp-≈ʳ braiding-selfInverse) , identity²)))) ⟩ 
    τ * ∘ M.F.₁ (σ ⊗₁ id) ∘ M.F.₁ (B⇐ ⊗₁ id) ∘ M.F.₁ associator.to ∘ M.F.₁ B⇒ ∘ M.F.₁ associator.to ∘ M.F.₁ (id ⊗₁ B⇒) 
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ((pullˡ hexagon₁') ○ pullʳ assoc²βε) ⟩ 
    τ * ∘ M.F.₁ (σ ⊗₁ id) ∘ M.F.₁ associator.to ∘ M.F.₁ (id ⊗₁ B⇐) ∘ M.F.₁ (id ⊗₁ B⇒) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimʳ (sym M.F.homomorphism ○ M.F.F-resp-≈ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identity² , (∘-resp-≈ˡ braiding-selfInverse ○ commutative)) ○ ⊗.identity) ○ M.F.identity) ⟩ 
    τ * ∘ M.F.₁ (σ ⊗₁ id) ∘ M.F.₁ associator.to 
      ∎
  
  ψ-assoc-to : ∀ {X Y Z} → M.F.₁ associator.to ∘ ψ ∘ (id ⊗₁ ψ) ≈ ψ {X ⊗₀ Y} {Z} ∘ (ψ ⊗₁ id) ∘ associator.to
  ψ-assoc-to = begin 
    M.F.₁ associator.to ∘ ψ ∘ (id ⊗₁ ψ) 
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ (sym ⊗.homomorphism) ○ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((elimˡ identity²) , refl))) ⟩ 
    M.F.₁ associator.to ∘ (τ * ∘ σ) ∘ (id ⊗₁ M.μ.η _) ∘ (id ⊗₁ M.F.₁ τ) ∘ (id ⊗₁ σ) 
      ≈⟨ pullˡ (pullˡ (F₁∘* ○ *-resp-≈ (RightStrength.strength-assoc rightStrength) ○ *-resp-≈ sym-assoc)) ○ sym (pullˡ *∘F₁ ○ (pullˡ *∘F₁ ○ sym-assoc)) ⟩
    τ * ∘ M.F.₁ (τ ⊗₁ id) ∘ M.F.₁ associator.to ∘ σ ∘ (id ⊗₁ M.μ.η _) ∘ (id ⊗₁ M.F.₁ τ) ∘ (id ⊗₁ σ) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ ((sym μ-η-comm) ○ sym-assoc) ⟩ 
    τ * ∘ M.F.₁ (τ ⊗₁ id) ∘ M.F.₁ associator.to ∘ σ * ∘ σ ∘ (id ⊗₁ M.F.₁ τ) ∘ (id ⊗₁ σ) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (σ.commute _) ⟩ 
    τ * ∘ M.F.₁ (τ ⊗₁ id) ∘ M.F.₁ associator.to ∘ σ * ∘ M.F.₁ (id ⊗₁ τ) ∘ σ ∘ (id ⊗₁ σ) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ pullˡ (assoc ○ σ-τ-assoc-to) ○ pullʳ assoc) ⟩ 
    τ * ∘ M.F.₁ (τ ⊗₁ id) ∘ τ * ∘ M.F.₁ (σ ⊗₁ id) ∘ M.F.₁ associator.to ∘ σ ∘ (id ⊗₁ σ) 
      ≈⟨ refl⟩∘⟨ extendʳ (F₁∘* ○ (*-resp-≈ (sym (τ.commute _)) ○ sym *∘F₁)) ⟩ 
    τ * ∘ τ * ∘ M.F.₁ (M.F.₁ τ ⊗₁ id) ∘ M.F.₁ (σ ⊗₁ id) ∘ M.F.₁ associator.to ∘ σ ∘ (id ⊗₁ σ) 
      ≈⟨ extendʳ (*-sym-assoc ○ *-resp-≈ (assoc ○ RightStrength.μ-η-comm rightStrength) ○ sym *∘F₁) ⟩ 
    τ * ∘ M.F.₁ (M.μ.η _ ⊗₁ id) ∘ M.F.₁ (M.F.₁ τ ⊗₁ id) ∘ M.F.₁ (σ ⊗₁ id) ∘ M.F.₁ associator.to ∘ σ ∘ (id ⊗₁ σ) 
      ≈⟨ refl⟩∘⟨ (pullˡ (sym M.F.homomorphism) ○ pullˡ (sym M.F.homomorphism) ○ ∘-resp-≈ˡ (M.F.F-resp-≈ (∘-resp-≈ˡ (sym ⊗.homomorphism) ○ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , (elimˡ identity²)))))) ⟩ 
    τ * ∘ M.F.₁ (ψ ⊗₁ id) ∘ M.F.₁ associator.to ∘ σ ∘ (id ⊗₁ σ) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ σ-strength-assoc' ⟩ 
    τ * ∘ M.F.₁ (ψ ⊗₁ id) ∘ σ ∘ associator.to 
      ≈⟨ ∘-resp-≈ʳ (extendʳ (sym (σ.commute _))) ○ (sym-assoc ○ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗.F-resp-≈ (refl , M.F.identity)))) ⟩ 
    ψ ∘ (ψ ⊗₁ id) ∘ associator.to 
      ∎

  ψ-assoc-from : ∀ {X Y Z} → M.F.₁ associator.from ∘ ψ {X ⊗₀ Y} {Z} ∘ (ψ ⊗₁ id) ≈ ψ ∘ (id ⊗₁ ψ) ∘ associator.from
  ψ-assoc-from = begin 
    M.F.₁ associator.from ∘ (τ * ∘ σ) ∘ (ψ ⊗₁ id) 
      ≈˘⟨ refl⟩∘⟨ sym commutes ⟩∘⟨ (pullˡ (sym ⊗.homomorphism) ○ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (sym commutes , (elimˡ identity²)))) ⟩ 
    M.F.₁ associator.from ∘ (σ * ∘ τ) ∘ (M.μ.η _ ⊗₁ id) ∘ (M.F.₁ σ ⊗₁ id) ∘ (τ ⊗₁ id) 
      ≈⟨ pullˡ (pullˡ (F₁∘* ○ *-resp-≈ strength-assoc ○ *-resp-≈ sym-assoc)) ○ sym (pullˡ *∘F₁ ○ (pullˡ *∘F₁ ○ sym-assoc)) ⟩
    σ * ∘ M.F.₁ (id ⊗₁ σ) ∘ M.F.₁ associator.from ∘ τ ∘ (M.μ.η _ ⊗₁ id) ∘ (M.F.₁ σ ⊗₁ id) ∘ (τ ⊗₁ id) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ ((sym (RightStrength.μ-η-comm rightStrength)) ○ sym-assoc) ⟩
    σ * ∘ M.F.₁ (id ⊗₁ σ) ∘ M.F.₁ associator.from ∘ τ * ∘ τ ∘ (M.F.₁ σ ⊗₁ id) ∘ (τ ⊗₁ id) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (τ.commute _) ⟩
    σ * ∘ M.F.₁ (id ⊗₁ σ) ∘ M.F.₁ associator.from ∘ τ * ∘ M.F.₁ (σ ⊗₁ id) ∘ τ ∘ (τ ⊗₁ id) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ pullˡ (assoc ○ τ-σ-assoc-from) ○ pullʳ assoc) ⟩
    σ * ∘ M.F.₁ (id ⊗₁ σ) ∘ σ * ∘ M.F.₁ (id ⊗₁ τ) ∘ M.F.₁ associator.from ∘ τ ∘ (τ ⊗₁ id) 
      ≈⟨ refl⟩∘⟨ extendʳ (F₁∘* ○ (*-resp-≈ (sym (σ.commute _)) ○ sym *∘F₁)) ⟩
    σ * ∘ σ * ∘ M.F.₁ (id ⊗₁ M.F.₁ σ) ∘ M.F.₁ (id ⊗₁ τ) ∘ M.F.₁ associator.from ∘ τ ∘ (τ ⊗₁ id) 
      ≈⟨ extendʳ (*-sym-assoc ○ *-resp-≈ (assoc ○ μ-η-comm) ○ sym *∘F₁) ⟩
    σ * ∘ M.F.₁ (id ⊗₁ M.μ.η _) ∘ M.F.₁ (id ⊗₁ M.F.₁ σ) ∘ M.F.₁ (id ⊗₁ τ) ∘ M.F.₁ associator.from ∘ τ ∘ (τ ⊗₁ id) 
      ≈⟨ (refl⟩∘⟨ (pullˡ (sym M.F.homomorphism) ○ pullˡ (sym M.F.homomorphism) ○ ∘-resp-≈ˡ (M.F.F-resp-≈ (∘-resp-≈ˡ (sym ⊗.homomorphism) ○ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (elimˡ identity² , sym commutes)))))) ⟩
    σ * ∘ M.F.₁ (id ⊗₁ ψ) ∘ M.F.₁ associator.from ∘ τ ∘ (τ ⊗₁ id) 
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ τ-strength-assoc' ⟩
    σ * ∘ M.F.₁ (id ⊗₁ ψ) ∘ τ ∘ associator.from 
      ≈⟨ (∘-resp-≈ʳ (extendʳ (sym (τ.commute _))) ○ (sym-assoc ○ extendʳ (sym commutes ⟩∘⟨ ⊗.F-resp-≈ (M.F.identity , refl)))) ⟩
    ψ ∘ (id ⊗₁ ψ) ∘ associator.from 
      ∎
