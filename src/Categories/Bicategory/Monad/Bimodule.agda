{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory

module Categories.Bicategory.Monad.Bimodule {o ℓ e t} {𝒞 : Bicategory o ℓ e t} where

open import Level
open import Categories.Bicategory.Monad using (Monad)
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands
import Categories.Morphism.Reasoning as MR

private
  module MR' {A B : Obj} where
    open MR (hom A B) using (pullˡ; elimʳ; assoc²βγ) public

record Bimodule (M₁ M₂ : Monad 𝒞) : Set (o ⊔ ℓ ⊔ e) where
  open Monad using (C; T; μ; η)
  field
    F       : C M₁ ⇒₁ C M₂
    actionˡ : F ∘₁ T M₁ ⇒₂ F
    actionʳ : T M₂ ∘₁ F ⇒₂ F

    assoc     : actionʳ ∘ᵥ (T M₂ ▷ actionˡ) ∘ᵥ α⇒ ≈ actionˡ ∘ᵥ (actionʳ ◁ T M₁)
    sym-assoc : actionˡ ∘ᵥ (actionʳ ◁ T M₁) ∘ᵥ α⇐ ≈ actionʳ ∘ᵥ (T M₂ ▷ actionˡ)

    assoc-actionˡ     : actionˡ ∘ᵥ (F ▷ μ M₁) ∘ᵥ α⇒ ≈ actionˡ ∘ᵥ (actionˡ ◁ T M₁)
    sym-assoc-actionˡ : actionˡ ∘ᵥ (actionˡ ◁ T M₁) ∘ᵥ α⇐ ≈ actionˡ ∘ᵥ (F ▷ μ M₁)
    assoc-actionʳ     : actionʳ ∘ᵥ (μ M₂ ◁ F) ∘ᵥ α⇐ ≈ actionʳ ∘ᵥ (T M₂ ▷ actionʳ)
    sym-assoc-actionʳ : actionʳ ∘ᵥ (T M₂ ▷ actionʳ) ∘ᵥ α⇒ ≈ actionʳ ∘ᵥ (μ M₂ ◁ F)

    identityˡ : actionˡ ∘ᵥ (F ▷ η M₁) ∘ᵥ unitorʳ.to ≈ id₂
    identityʳ : actionʳ ∘ᵥ (η M₂ ◁ F) ∘ᵥ unitorˡ.to ≈ id₂

id-bimodule : (M : Monad 𝒞) → Bimodule M M
id-bimodule M = record
  { F = T
  ; actionˡ = μ
  ; actionʳ = μ
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; assoc-actionˡ = assoc
  ; sym-assoc-actionˡ = sym-assoc
  ; assoc-actionʳ = sym-assoc
  ; sym-assoc-actionʳ = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  }
  where
    open Monad M
