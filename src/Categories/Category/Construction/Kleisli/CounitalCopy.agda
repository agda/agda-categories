{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Kleisli.CounitalCopy where

open import Level

open import Categories.Category
open import Categories.Monad hiding (id)
open import Categories.Monad.Strong
open import Categories.Monad.Strong.Properties
open import Categories.Monad.Commutative
open import Categories.Monad.Commutative.Properties
open import Categories.Monad.EquationalLifting
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.SymmetricMonoidal
open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.BinaryProducts
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.CounitalCopy
open import Categories.Object.Terminal
open import Categories.NaturalTransformation.Core using (ntHelper)
open import Categories.Category.Construction.Kleisli.Monoidal
open import Categories.Category.Construction.Kleisli.Symmetric


open import Data.Product using (_,_)

import Categories.Morphism.Reasoning as MR

import Categories.Monad.Strong.Properties as StrongProps

private
  variable
    o ℓ e : Level

module _ {𝒞 : Category o ℓ e} (cartesian : Cartesian 𝒞) (ELM : EquationalLiftingMonad cartesian) where
  open Category 𝒞
  open MR 𝒞
  open HomReasoning
  open Equiv
  open Cartesian cartesian
  open Terminal terminal
  open BinaryProducts products renaming (η to prod-η)

  open EquationalLiftingMonad ELM hiding (identityˡ)
  -- open CommutativeMonad CM hiding (identityˡ)
  open Monad M using (μ)
  open TripleNotation M

  open StrongProps.Left strength using (left-right-braiding-comm; right-left-braiding-comm)
  open StrongProps.Left.Shorthands strength
  open StrongProps.Right.Shorthands rightStrength

  open CartesianMonoidal cartesian using (monoidal)
  open Monoidal monoidal
  open Symmetric (symmetric 𝒞 cartesian) using (braided; hexagon₁; hexagon₂)

  open CommutativeProperties braided commutativeMonad

  Kleisli-CounitalCopy : CounitalCopy (Kleisli M)
  Kleisli-CounitalCopy = record
    { monoidal = Kleisli-Monoidal cartesian commutativeMonad
    ; symmetric = Kleisli-Symmetric cartesian commutativeMonad
    ; isMonoid = λ X → record
        { μ = η ∘ ⟨ id , id ⟩ 
        ; η = η ∘ ! 
        ; assoc = begin 
          (ψ ∘ ((η ∘ ⟨ id , id ⟩) ⁂ η)) * ∘ η ∘ ⟨ id , id ⟩ 
            ≈⟨ pullˡ *-identityʳ ⟩ 
          (ψ ∘ ((η ∘ ⟨ id , id ⟩) ⁂ η)) ∘ ⟨ id , id ⟩ 
            ≈⟨ pullʳ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityʳ refl ○ sym ⁂∘⟨⟩) ⟩ 
          ψ ∘ (η ⁂ η) ∘ ⟨ ⟨ id , id ⟩ , id ⟩ 
            ≈⟨ pullˡ ψ-η ⟩ 
          η ∘ ⟨ ⟨ id , id ⟩ , id ⟩ 
            ≈˘⟨ pullʳ assocʳ∘⟨⟩ ⟩ 
          (η ∘ associator.to) ∘ ⟨ id , ⟨ id , id ⟩ ⟩ 
            ≈˘⟨ pullˡ *-identityʳ ⟩ 
          (η ∘ associator.to) * ∘ η ∘ ⟨ id , ⟨ id , id ⟩ ⟩ 
            ≈˘⟨ refl⟩∘⟨ pullˡ ψ-η ⟩ 
          (η ∘ associator.to) * ∘ ψ ∘ (η ⁂ η) ∘ ⟨ id , ⟨ id , id ⟩ ⟩ 
            ≈˘⟨ pullʳ (pullʳ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ refl identityʳ ○ sym ⁂∘⟨⟩)) ⟩ 
          ((η ∘ associator.to) * ∘ ψ ∘ (η ⁂ (η ∘ ⟨ id , id ⟩))) ∘ ⟨ id , id ⟩ 
            ≈˘⟨ pullˡ *-identityʳ ⟩ 
          ((η ∘ associator.to) * ∘ ψ ∘ (η ⁂ (η ∘ ⟨ id , id ⟩))) * ∘ η ∘ ⟨ id , id ⟩ 
            ∎ 
        ; identityˡ = begin 
          η ∘ ⟨ ! , id ⟩ 
            ≈˘⟨ pullˡ ψ-η ⟩ 
          ψ ∘ (η ⁂ η) ∘ ⟨ ! , id ⟩ 
            ≈˘⟨ pullʳ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityʳ identityʳ ○ sym (⁂∘⟨⟩ ○ ⟨⟩-cong₂ refl identityʳ)) ⟩ 
          (ψ ∘ ((η ∘ !) ⁂ η)) ∘ ⟨ id , id ⟩ 
            ≈˘⟨ pullˡ *-identityʳ ⟩ 
          (ψ ∘ ((η ∘ !) ⁂ η)) * ∘ η ∘ ⟨ id , id ⟩ 
            ∎ 
        ; identityʳ = begin 
          η ∘ ⟨ id , ! ⟩ 
            ≈˘⟨ pullˡ ψ-η ⟩ 
          ψ ∘ (η ⁂ η) ∘ ⟨ id , ! ⟩ 
            ≈˘⟨ pullʳ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ refl identityʳ ○ sym ⁂∘⟨⟩) ⟩ 
          (ψ ∘ (η ⁂ (η ∘ !))) ∘ ⟨ id , id ⟩ 
            ≈˘⟨ pullˡ *-identityʳ ⟩ 
          (ψ ∘ (η ⁂ (η ∘ !))) * ∘ η ∘ ⟨ id , id ⟩ 
            ∎ 
        }
    ; natural = λ {X} {f} → begin 
      (η ∘ Δ) * ∘ f         ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ Δ ∘ f           ≈˘⟨ pullˡ ψ-lifting ⟩ 
      ψ ∘ Δ ∘ f             ≈˘⟨ pullʳ (⁂∘Δ ○ sym Δ∘) ⟩ 
      (ψ ∘ (f ⁂ f)) ∘ Δ     ≈˘⟨ pullˡ *-identityʳ ⟩ 
    (ψ ∘ (f ⁂ f)) * ∘ η ∘ Δ ∎
    ; inverse₁ = begin 
      (η ∘ Δ) * ∘ (η ∘ unitorˡ.from) ≈⟨ pullˡ *-identityʳ ⟩ 
      (η ∘ Δ) ∘ π₂                   ≈⟨ pullʳ (∘-resp-≈ˡ (⟨⟩-cong₂ (sym (!-unique _)) refl)) ⟩ 
      η ∘ ⟨ ! , id ⟩ ∘ π₂            ≈⟨ elimʳ unitorˡ.isoˡ ⟩
      η                              ∎
    ; inverse₂ = begin 
      ((η ∘ π₂) *) ∘ η ∘ ⟨ id , id ⟩ ≈⟨ pullˡ *-identityʳ ⟩ 
      (η ∘ π₂) ∘ ⟨ id , id ⟩         ≈⟨ cancelʳ project₂ ⟩ 
      η                              ∎
    ; preserves = begin 
      (η ∘ associator.to) * ∘ (ψ ∘ (η ⁂ (η ∘ associator.from))) * ∘ (ψ ∘ (η ⁂ ((ψ ∘ ((η ∘ swap) ⁂ η)) * ∘ η ∘ associator.to))) * ∘ (η ∘ associator.from) * ∘ (ψ ∘ ((η ∘ Δ) ⁂ (η ∘ Δ))) 
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ∘-resp-≈ʳ ⁂∘⁂ ⟩ 
      (η ∘ associator.to) * ∘ (ψ ∘ (η ⁂ (η ∘ associator.from))) * ∘ (ψ ∘ (η ⁂ ((ψ ∘ ((η ∘ swap) ⁂ η)) * ∘ η ∘ associator.to))) * ∘ (η ∘ associator.from) * ∘ (ψ ∘ (η ⁂ η) ∘ (Δ ⁂ Δ)) 
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ψ-η ⟩ 
      (η ∘ associator.to) * ∘ (ψ ∘ (η ⁂ (η ∘ associator.from))) * ∘ (ψ ∘ (η ⁂ ((ψ ∘ ((η ∘ swap) ⁂ η)) * ∘ η ∘ associator.to))) * ∘ (η ∘ associator.from) * ∘ (η ∘ (Δ ⁂ Δ)) 
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ *-identityʳ ⟩ 
      (η ∘ associator.to) * ∘ (ψ ∘ (η ⁂ (η ∘ associator.from))) * ∘ (ψ ∘ (η ⁂ ((ψ ∘ ((η ∘ swap) ⁂ η)) * ∘ η ∘ associator.to))) * ∘ (η ∘ associator.from) ∘ (Δ ⁂ Δ) 
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (pullˡ *-identityʳ) ⟩ 
      (η ∘ associator.to) * ∘ (ψ ∘ (η ⁂ (η ∘ associator.from))) * ∘ ((ψ ∘ (η ⁂ ((ψ ∘ ((η ∘ swap) ⁂ η)) * ∘ η ∘ associator.to))) ∘ associator.from) ∘ (Δ ⁂ Δ) 
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ (⁂-cong₂ refl (∘-resp-≈ˡ (*-resp-≈ (∘-resp-≈ʳ (⁂∘⁂ ○ ⁂-cong₂ refl identityʳ)))))) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
      (η ∘ associator.to) * ∘ (ψ ∘ (η ⁂ (η ∘ associator.from))) * ∘ ((ψ ∘ (η ⁂ ((ψ ∘ (η ⁂ η) ∘ (swap ⁂ id)) * ∘ η ∘ associator.to))) ∘ associator.from) ∘ (Δ ⁂ Δ) 
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ (⁂-cong₂ refl (∘-resp-≈ˡ (*-resp-≈ (pullˡ ψ-η))))) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
      (η ∘ associator.to) * ∘ (ψ ∘ (η ⁂ (η ∘ associator.from))) * ∘ ((ψ ∘ (η ⁂ ((η ∘ (swap ⁂ id)) * ∘ η ∘ associator.to))) ∘ associator.from) ∘ (Δ ⁂ Δ)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ (⁂-cong₂ refl (pullˡ *-identityʳ ○ assoc))) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
      (η ∘ associator.to) * ∘ (ψ ∘ (η ⁂ (η ∘ associator.from))) * ∘ ((ψ ∘ (η ⁂ (η ∘ (swap ⁂ id) ∘ associator.to))) ∘ associator.from) ∘ (Δ ⁂ Δ)
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ (⁂∘⁂ ○ ⁂-cong₂ identityʳ refl)) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
      (η ∘ associator.to) * ∘ (ψ ∘ (η ⁂ (η ∘ associator.from))) * ∘ ((ψ ∘ (η ⁂ η) ∘ (id ⁂ ((swap ⁂ id) ∘ associator.to))) ∘ associator.from) ∘ (Δ ⁂ Δ)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ ψ-η ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
      (η ∘ associator.to) * ∘ (ψ ∘ (η ⁂ (η ∘ associator.from))) * ∘ ((η ∘ (id ⁂ ((swap ⁂ id) ∘ associator.to))) ∘ associator.from) ∘ (Δ ⁂ Δ)
        ≈⟨ refl⟩∘⟨ (pullˡ (pullˡ (pullˡ *-identityʳ))) ⟩ 
      (η ∘ associator.to) * ∘ (((ψ ∘ (η ⁂ (η ∘ associator.from))) ∘ (id ⁂ (swap ⁂ id) ∘ associator.to)) ∘ associator.from) ∘ (Δ ⁂ Δ)
        ≈˘⟨ refl⟩∘⟨ (((∘-resp-≈ʳ (⁂∘⁂ ○ ⁂-cong₂ identityʳ refl)) ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
      (η ∘ associator.to) * ∘ (((ψ ∘ (η ⁂ η) ∘ (id ⁂ associator.from)) ∘ (id ⁂ (swap ⁂ id) ∘ associator.to)) ∘ associator.from) ∘ (Δ ⁂ Δ)
        ≈⟨ refl⟩∘⟨ ((pullˡ ψ-η ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
      (η ∘ associator.to) * ∘ (((η ∘ (id ⁂ associator.from)) ∘ (id ⁂ (swap ⁂ id) ∘ associator.to)) ∘ associator.from) ∘ (Δ ⁂ Δ)
        ≈⟨ pullˡ (pullˡ (pullˡ (pullˡ *-identityʳ))) ⟩ 
      ((((η ∘ associator.to) ∘ (id ⁂ associator.from)) ∘ (id ⁂ (swap ⁂ id) ∘ associator.to)) ∘ associator.from) ∘ (Δ ⁂ Δ)
        ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (⟨⟩∘ ○ ⟨⟩-cong₂ identityˡ identityˡ) (⟨⟩∘ ○ ⟨⟩-cong₂ identityˡ identityˡ) ⟩ 
      ((((η ∘ associator.to) ∘ (id ⁂ associator.from)) ∘ (id ⁂ (swap ⁂ id) ∘ associator.to)) ∘ associator.from) ∘ ⟨ ⟨ π₁ , π₁ ⟩ , ⟨ π₂ , π₂ ⟩ ⟩
        ≈⟨ pullʳ assocˡ∘⟨⟩ ⟩ 
      (((η ∘ associator.to) ∘ (id ⁂ associator.from)) ∘ (id ⁂ (swap ⁂ id) ∘ associator.to)) ∘ ⟨ π₁ , ⟨ π₁ , ⟨ π₂ , π₂ ⟩ ⟩ ⟩
        ≈⟨ pullʳ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityˡ (pullʳ assocʳ∘⟨⟩)) ⟩ 
      ((η ∘ associator.to) ∘ (id ⁂ associator.from)) ∘ ⟨ π₁ , (swap ⁂ id) ∘ ⟨ ⟨ π₁ , π₂ ⟩ , π₂ ⟩ ⟩
        ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ refl (⁂∘⟨⟩ ○ ⟨⟩-cong₂ swap∘⟨⟩ identityˡ) ⟩ 
      ((η ∘ associator.to) ∘ (id ⁂ associator.from)) ∘ ⟨ π₁ , ⟨ ⟨ π₂ , π₁ ⟩ , π₂ ⟩ ⟩
        ≈⟨ pullʳ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityˡ assocˡ∘⟨⟩) ⟩ 
      (η ∘ associator.to) ∘ ⟨ π₁ , ⟨ π₂ , ⟨ π₁ , π₂ ⟩ ⟩ ⟩
        ≈⟨ pullʳ assocʳ∘⟨⟩ ⟩ 
      η ∘ ⟨ ⟨ π₁ , π₂ ⟩ , ⟨ π₁ , π₂ ⟩ ⟩
        ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ prod-η prod-η ⟩ 
      η ∘ Δ 
        ∎
    }

