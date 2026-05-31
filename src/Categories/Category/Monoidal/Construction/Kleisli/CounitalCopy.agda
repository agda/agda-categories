{-# OPTIONS --without-K --safe #-}
module Categories.Category.Monoidal.Construction.Kleisli.CounitalCopy where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong.Properties
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Commutative.Properties using (module CommutativeProperties)
open import Categories.Monad.EquationalLifting using (EquationalLiftingMonad)
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Cartesian.SymmetricMonoidal using (symmetric)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.CounitalCopy using (CounitalCopy)
open import Categories.Object.Terminal using (Terminal)
open import Categories.Object.Monoid using (IsMonoid)
open import Categories.Category.Monoidal.Construction.Kleisli using (Kleisli-Monoidal)
open import Categories.Category.Monoidal.Construction.Kleisli.Symmetric using (Kleisli-Symmetric)

import Categories.Morphism.Reasoning as MR
import Categories.Monad.Strong.Properties as StrongProps
import Categories.Category.Monoidal.Utilities as MonoidalUtils

private
  variable
    o ℓ e : Level

-- The Kleisli category of an equational lifting monad is a counital copy category.

module _ {𝒞 : Category o ℓ e} (cartesian : Cartesian 𝒞) (ELM : EquationalLiftingMonad cartesian) where
  open Category 𝒞
  open MR 𝒞
  open HomReasoning
  open Equiv
  open Cartesian cartesian renaming (η to prod-η)

  open EquationalLiftingMonad ELM hiding (identityˡ)
  open Monad M using (μ)
  open TripleNotation M

  open StrongProps.Left strength using (left-right-braiding-comm; right-left-braiding-comm)
  open StrongProps.Left.Shorthands strength
  open StrongProps.Right.Shorthands rightStrength

  open CartesianMonoidal cartesian using (monoidal)
  open Monoidal monoidal using (associator; unitorˡ)
  open MonoidalUtils monoidal using (module Shorthands)
  open Shorthands
  open Symmetric (symmetric 𝒞 cartesian) using (braided)
  open CommutativeProperties braided commutativeMonad

  open import Categories.Category.Monoidal.Properties (Kleisli-Monoidal (symmetric 𝒞 cartesian) commutativeMonad) using (monoidal-Op)


  Kleisli-IsComonoid : ∀ X → IsMonoid (monoidal-Op) X
  Kleisli-IsComonoid X = record
    { μ = η ∘ ⟨ id , id ⟩ 
    ; η = η ∘ ! 
    ; assoc = assoc'
    ; identityˡ = identityˡ' 
    ; identityʳ = identityʳ'
    }
    where
    assoc' : (ψ ∘ ((η ∘ ⟨ id , id ⟩) ×₁ η)) * ∘ η ∘ ⟨ id , id ⟩
           ≈ ((η ∘ α⇐) * ∘ ψ ∘ (η ×₁ (η ∘ ⟨ id , id ⟩))) * ∘ η ∘ ⟨ id , id ⟩
    assoc' = begin 
      (ψ ∘ ((η ∘ ⟨ id , id ⟩) ×₁ η)) * ∘ η ∘ ⟨ id , id ⟩ 
        ≈⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ ((η ∘ ⟨ id , id ⟩) ×₁ η)) ∘ ⟨ id , id ⟩ 
        ≈⟨ pullʳ (×₁∘⟨⟩ ○ ⟨⟩-cong₂ identityʳ refl ○ sym ×₁∘⟨⟩) ⟩ 
      ψ ∘ (η ×₁ η) ∘ ⟨ ⟨ id , id ⟩ , id ⟩ 
        ≈⟨ pullˡ ψ-η ⟩ 
      η ∘ ⟨ ⟨ id , id ⟩ , id ⟩ 
        ≈˘⟨ pullʳ assocʳ∘⟨⟩ ⟩ 
      (η ∘ α⇐) ∘ ⟨ id , ⟨ id , id ⟩ ⟩ 
        ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (η ∘ α⇐) * ∘ η ∘ ⟨ id , ⟨ id , id ⟩ ⟩ 
        ≈˘⟨ refl⟩∘⟨ pullˡ ψ-η ⟩ 
      (η ∘ α⇐) * ∘ ψ ∘ (η ×₁ η) ∘ ⟨ id , ⟨ id , id ⟩ ⟩ 
        ≈˘⟨ pullʳ (pullʳ (×₁∘⟨⟩ ○ ⟨⟩-cong₂ refl identityʳ ○ sym ×₁∘⟨⟩)) ⟩ 
      ((η ∘ α⇐) * ∘ ψ ∘ (η ×₁ (η ∘ ⟨ id , id ⟩))) ∘ ⟨ id , id ⟩ 
        ≈˘⟨ pullˡ *-identityʳ ⟩ 
      ((η ∘ α⇐) * ∘ ψ ∘ (η ×₁ (η ∘ ⟨ id , id ⟩))) * ∘ η ∘ ⟨ id , id ⟩ 
        ∎ 
    identityˡ' : η ∘ ⟨ ! , id ⟩ ≈ (ψ ∘ ((η ∘ !) ×₁ η)) * ∘ η ∘ ⟨ id , id ⟩
    identityˡ' = begin 
      η ∘ ⟨ ! , id ⟩ 
        ≈˘⟨ pullˡ ψ-η ⟩ 
      ψ ∘ (η ×₁ η) ∘ ⟨ ! , id ⟩ 
        ≈˘⟨ pullʳ (×₁∘⟨⟩ ○ ⟨⟩-cong₂ identityʳ identityʳ ○ sym (×₁∘⟨⟩ ○ ⟨⟩-cong₂ refl identityʳ)) ⟩ 
      (ψ ∘ ((η ∘ !) ×₁ η)) ∘ ⟨ id , id ⟩ 
        ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ ((η ∘ !) ×₁ η)) * ∘ η ∘ ⟨ id , id ⟩ 
        ∎
    identityʳ' : η ∘ ⟨ id , ! ⟩ ≈ (ψ ∘ (η ×₁ (η ∘ !))) * ∘ η ∘ ⟨ id , id ⟩
    identityʳ' = begin 
      η ∘ ⟨ id , ! ⟩ 
        ≈˘⟨ pullˡ ψ-η ⟩ 
      ψ ∘ (η ×₁ η) ∘ ⟨ id , ! ⟩ 
        ≈˘⟨ pullʳ (×₁∘⟨⟩ ○ ⟨⟩-cong₂ refl identityʳ ○ sym ×₁∘⟨⟩) ⟩ 
      (ψ ∘ (η ×₁ (η ∘ !))) ∘ ⟨ id , id ⟩ 
        ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (η ×₁ (η ∘ !))) * ∘ η ∘ ⟨ id , id ⟩ 
        ∎ 

  Kleisli-CounitalCopy : CounitalCopy (Kleisli-Symmetric (symmetric 𝒞 cartesian) commutativeMonad)
  Kleisli-CounitalCopy = record
    { isComonoid = Kleisli-IsComonoid
    ; natural = natural'
    ; inverse₁ = inverse₁'
    ; inverse₂ = inverse₂'
    ; cocommutative = cocommutative'
    ; preserves = preserves'
    }
    where
    natural' : ∀ {A B} (f : A ⇒ M.F.₀ B) → (η ∘ Δ) * ∘ f ≈ (ψ ∘ (f ×₁ f)) * ∘ η ∘ Δ
    natural' f = begin 
      (η ∘ Δ) * ∘ f           ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ Δ ∘ f             ≈˘⟨ pullˡ ψ-lifting ⟩ 
      ψ ∘ Δ ∘ f               ≈˘⟨ pullʳ (×₁∘Δ ○ sym Δ∘) ⟩ 
      (ψ ∘ (f ×₁ f)) ∘ Δ       ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (f ×₁ f)) * ∘ η ∘ Δ ∎
    inverse₁' : (η ∘ Δ) * ∘ (η ∘ λ⇒) ≈ η
    inverse₁' = begin 
      (η ∘ Δ) * ∘ (η ∘ λ⇒) ≈⟨ pullˡ *-identityʳ ⟩ 
      (η ∘ Δ) ∘ π₂         ≈⟨ pullʳ (∘-resp-≈ˡ (⟨⟩-cong₂ (sym (!-unique _)) refl)) ⟩ 
      η ∘ ⟨ ! , id ⟩ ∘ π₂  ≈⟨ elimʳ unitorˡ.isoˡ ⟩
      η                    ∎
    inverse₂' : ((η ∘ π₂) *) ∘ η ∘ ⟨ id , id ⟩ ≈ η
    inverse₂' = begin 
      ((η ∘ π₂) *) ∘ η ∘ ⟨ id , id ⟩ ≈⟨ pullˡ *-identityʳ ⟩ 
      (η ∘ π₂) ∘ ⟨ id , id ⟩         ≈⟨ cancelʳ project₂ ⟩ 
      η                              ∎
    cocommutative' : ∀ {A} → (η ∘ swap) * ∘ η ∘ ⟨ id , id ⟩ ≈ η ∘ ⟨ id {A} , id {A} ⟩
    cocommutative' = begin 
      (η ∘ swap) * ∘ η ∘ ⟨ id , id ⟩ ≈⟨ extendʳ *-identityʳ ⟩ 
      η ∘ swap ∘ ⟨ id , id ⟩         ≈⟨ refl⟩∘⟨ swap∘⟨⟩ ⟩ 
      η ∘ ⟨ id , id ⟩                ∎
    preserves' : ∀ {X Y} → (η ∘ α⇐) * ∘ (ψ ∘ (η ×₁ (η ∘ α⇒))) * ∘ (ψ ∘ (η ×₁ ((ψ ∘ ((η ∘ swap) ×₁ η)) * ∘ η ∘ α⇐))) * ∘ (η ∘ α⇒) * ∘ (ψ ∘ ((η ∘ Δ) ×₁ (η ∘ Δ)))
               ≈ η ∘ Δ {X × Y}
    preserves' = begin 
      (η ∘ α⇐) * ∘ (ψ ∘ (η ×₁ (η ∘ α⇒))) * ∘ (ψ ∘ (η ×₁ ((ψ ∘ ((η ∘ swap) ×₁ η)) * ∘ η ∘ α⇐))) * ∘ (η ∘ α⇒) * ∘ (ψ ∘ ((η ∘ Δ) ×₁ (η ∘ Δ))) 
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ helper ⟩ 
      (η ∘ α⇐) * ∘ (ψ ∘ (η ×₁ (η ∘ α⇒))) * ∘ ((η ∘ (id ×₁ ((swap ×₁ id) ∘ α⇐))) ∘ α⇒) ∘ (Δ ×₁ Δ)
        ≈⟨ refl⟩∘⟨ (pullˡ (pullˡ (pullˡ *-identityʳ))) ⟩ 
      (η ∘ α⇐) * ∘ (((ψ ∘ (η ×₁ (η ∘ α⇒))) ∘ (id ×₁ (swap ×₁ id) ∘ α⇐)) ∘ α⇒) ∘ (Δ ×₁ Δ)
        ≈˘⟨ refl⟩∘⟨ (((∘-resp-≈ʳ (×₁∘×₁ ○ ×₁-cong₂ identityʳ refl)) ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
      (η ∘ α⇐) * ∘ (((ψ ∘ (η ×₁ η) ∘ (id ×₁ α⇒)) ∘ (id ×₁ (swap ×₁ id) ∘ α⇐)) ∘ α⇒) ∘ (Δ ×₁ Δ)
        ≈⟨ refl⟩∘⟨ ((pullˡ ψ-η ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
      (η ∘ α⇐) * ∘ (((η ∘ (id ×₁ α⇒)) ∘ (id ×₁ (swap ×₁ id) ∘ α⇐)) ∘ α⇒) ∘ (Δ ×₁ Δ)
        ≈⟨ pullˡ (pullˡ (pullˡ (pullˡ *-identityʳ))) ⟩ 
      ((((η ∘ α⇐) ∘ (id ×₁ α⇒)) ∘ (id ×₁ (swap ×₁ id) ∘ α⇐)) ∘ α⇒) ∘ (Δ ×₁ Δ)
        ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (⟨⟩∘ ○ ⟨⟩-cong₂ identityˡ identityˡ) (⟨⟩∘ ○ ⟨⟩-cong₂ identityˡ identityˡ) ⟩ 
      ((((η ∘ α⇐) ∘ (id ×₁ α⇒)) ∘ (id ×₁ (swap ×₁ id) ∘ α⇐)) ∘ α⇒) ∘ ⟨ ⟨ π₁ , π₁ ⟩ , ⟨ π₂ , π₂ ⟩ ⟩
        ≈⟨ pullʳ assocˡ∘⟨⟩ ⟩ 
      (((η ∘ α⇐) ∘ (id ×₁ α⇒)) ∘ (id ×₁ (swap ×₁ id) ∘ α⇐)) ∘ ⟨ π₁ , ⟨ π₁ , ⟨ π₂ , π₂ ⟩ ⟩ ⟩
        ≈⟨ pullʳ (×₁∘⟨⟩ ○ ⟨⟩-cong₂ identityˡ (pullʳ assocʳ∘⟨⟩)) ⟩ 
      ((η ∘ α⇐) ∘ (id ×₁ α⇒)) ∘ ⟨ π₁ , (swap ×₁ id) ∘ ⟨ ⟨ π₁ , π₂ ⟩ , π₂ ⟩ ⟩
        ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ refl (×₁∘⟨⟩ ○ ⟨⟩-cong₂ swap∘⟨⟩ identityˡ) ⟩ 
      ((η ∘ α⇐) ∘ (id ×₁ α⇒)) ∘ ⟨ π₁ , ⟨ ⟨ π₂ , π₁ ⟩ , π₂ ⟩ ⟩
        ≈⟨ pullʳ (×₁∘⟨⟩ ○ ⟨⟩-cong₂ identityˡ assocˡ∘⟨⟩) ⟩ 
      (η ∘ α⇐) ∘ ⟨ π₁ , ⟨ π₂ , ⟨ π₁ , π₂ ⟩ ⟩ ⟩
        ≈⟨ pullʳ assocʳ∘⟨⟩ ⟩ 
      η ∘ ⟨ ⟨ π₁ , π₂ ⟩ , ⟨ π₁ , π₂ ⟩ ⟩
        ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ prod-η prod-η ⟩ 
      η ∘ Δ 
        ∎
      where
      helper : (ψ ∘ (η ×₁ ((ψ ∘ ((η ∘ swap) ×₁ η)) * ∘ η ∘ α⇐))) * ∘ (η ∘ α⇒) * ∘ (ψ ∘ ((η ∘ Δ) ×₁ (η ∘ Δ))) ≈ ((η ∘ (id ×₁ ((swap ×₁ id) ∘ α⇐))) ∘ α⇒) ∘ (Δ ×₁ Δ)
      helper = begin
        (ψ ∘ (η ×₁ ((ψ ∘ ((η ∘ swap) ×₁ η)) * ∘ η ∘ α⇐))) * ∘ (η ∘ α⇒) * ∘ (ψ ∘ ((η ∘ Δ) ×₁ (η ∘ Δ))) 
          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ∘-resp-≈ʳ ×₁∘×₁ ⟩ 
        (ψ ∘ (η ×₁ ((ψ ∘ ((η ∘ swap) ×₁ η)) * ∘ η ∘ α⇐))) * ∘ (η ∘ α⇒) * ∘ (ψ ∘ (η ×₁ η) ∘ (Δ ×₁ Δ)) 
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ψ-η ⟩ 
        (ψ ∘ (η ×₁ ((ψ ∘ ((η ∘ swap) ×₁ η)) * ∘ η ∘ α⇐))) * ∘ (η ∘ α⇒) * ∘ (η ∘ (Δ ×₁ Δ)) 
          ≈⟨ refl⟩∘⟨ pullˡ *-identityʳ ⟩ 
        (ψ ∘ (η ×₁ ((ψ ∘ ((η ∘ swap) ×₁ η)) * ∘ η ∘ α⇐))) * ∘ (η ∘ α⇒) ∘ (Δ ×₁ Δ) 
          ≈⟨ pullˡ (pullˡ *-identityʳ) ⟩ 
        ((ψ ∘ (η ×₁ ((ψ ∘ ((η ∘ swap) ×₁ η)) * ∘ η ∘ α⇐))) ∘ α⇒) ∘ (Δ ×₁ Δ) 
          ≈˘⟨ ((refl⟩∘⟨ (×₁-cong₂ refl (∘-resp-≈ˡ (*-resp-≈ (∘-resp-≈ʳ (×₁∘×₁ ○ ×₁-cong₂ refl identityʳ)))))) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
        ((ψ ∘ (η ×₁ ((ψ ∘ (η ×₁ η) ∘ (swap ×₁ id)) * ∘ η ∘ α⇐))) ∘ α⇒) ∘ (Δ ×₁ Δ) 
          ≈⟨ ((refl⟩∘⟨ (×₁-cong₂ refl (∘-resp-≈ˡ (*-resp-≈ (pullˡ ψ-η))))) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
        ((ψ ∘ (η ×₁ ((η ∘ (swap ×₁ id)) * ∘ η ∘ α⇐))) ∘ α⇒) ∘ (Δ ×₁ Δ)
          ≈⟨ ((refl⟩∘⟨ (×₁-cong₂ refl (pullˡ *-identityʳ ○ assoc))) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
        ((ψ ∘ (η ×₁ (η ∘ (swap ×₁ id) ∘ α⇐))) ∘ α⇒) ∘ (Δ ×₁ Δ)
          ≈˘⟨ ((refl⟩∘⟨ (×₁∘×₁ ○ ×₁-cong₂ identityʳ refl)) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
        ((ψ ∘ (η ×₁ η) ∘ (id ×₁ ((swap ×₁ id) ∘ α⇐))) ∘ α⇒) ∘ (Δ ×₁ Δ)
          ≈⟨ (pullˡ ψ-η ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
        ((η ∘ (id ×₁ ((swap ×₁ id) ∘ α⇐))) ∘ α⇒) ∘ (Δ ×₁ Δ)
          ∎


