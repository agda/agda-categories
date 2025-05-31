{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory

module Categories.Bicategory.Monad.Bimodule {o ℓ e t} {𝒞 : Bicategory o ℓ e t} where

open import Level
open import Categories.Bicategory.Monad
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞

record Bimodule (M₁ M₂ : Monad 𝒞) : Set (o ⊔ ℓ ⊔ e) where
  open Monad M₁ renaming (C to C₁; T to T₁; μ to μ₁; η to η₁)
  open Monad M₂ renaming (C to C₂; T to T₂; μ to μ₂; η to η₂)

  field
    F       : C₁ ⇒₁ C₂
    actionˡ : F ∘₁ T₁ ⇒₂ F
    actionʳ : T₂ ∘₁ F ⇒₂ F

    assoc     : actionʳ ∘ᵥ (T₂ ▷ actionˡ) ∘ᵥ associator.from ≈ actionˡ ∘ᵥ (actionʳ ◁ T₁)
    sym-assoc : actionˡ ∘ᵥ (actionʳ ◁ T₁) ∘ᵥ associator.to ≈ actionʳ ∘ᵥ (T₂ ▷ actionˡ)

    assoc-actionˡ     : actionˡ ∘ᵥ (F ▷ μ₁) ∘ᵥ associator.from ≈ actionˡ ∘ᵥ (actionˡ ◁ T₁)
    sym-assoc-actionˡ : actionˡ ∘ᵥ (actionˡ ◁ T₁) ∘ᵥ associator.to ≈ actionˡ ∘ᵥ (F ▷ μ₁)
    assoc-actionʳ     : actionʳ ∘ᵥ (μ₂ ◁ F) ∘ᵥ associator.to ≈ actionʳ ∘ᵥ (T₂ ▷ actionʳ)
    sym-assoc-actionʳ : actionʳ ∘ᵥ (T₂ ▷ actionʳ) ∘ᵥ associator.from ≈ actionʳ ∘ᵥ (μ₂ ◁ F)

    identityˡ : actionˡ ∘ᵥ (F ▷ η₁) ∘ᵥ unitorʳ.to ≈ id₂
    identityʳ : actionʳ ∘ᵥ (η₂ ◁ F) ∘ᵥ unitorˡ.to ≈ id₂

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
  where open Monad M

record Bimodulehomomorphism {M₁ M₂ : Monad 𝒞} (B₁ B₂ : Bimodule M₁ M₂) : Set (ℓ ⊔ e) where
  open Monad M₁ renaming (C to C₁; T to T₁)
  open Monad M₂ renaming (C to C₂; T to T₂)
  open Bimodule B₁ renaming (F to F₁; actionˡ to actionˡ₁; actionʳ to actionʳ₁)
  open Bimodule B₂ renaming (F to F₂; actionˡ to actionˡ₂; actionʳ to actionʳ₂)
  field
    α       : F₁ ⇒₂ F₂
    linearˡ : actionˡ₂ ∘ᵥ (α ◁ T₁) ≈ α ∘ᵥ actionˡ₁
    linearʳ : actionʳ₂ ∘ᵥ (T₂ ▷ α) ≈ α ∘ᵥ actionʳ₁

open import Categories.Category

id-bimodule-hom : {M₁ M₂ : Monad 𝒞} → {B : Bimodule M₁ M₂} → Bimodulehomomorphism B B
id-bimodule-hom {M₁} {M₂} {B} = record
  { α = id₂
  ; linearˡ = begin
      actionˡ ∘ᵥ (id₂ ◁ T₁) ≈⟨ refl⟩∘⟨ id₂◁ ⟩
      actionˡ ∘ᵥ id₂        ≈⟨ identity₂ʳ ⟩
      actionˡ               ≈⟨ hom.Equiv.sym identity₂ˡ ⟩
      id₂ ∘ᵥ actionˡ        ∎
  ; linearʳ = begin
      actionʳ ∘ᵥ (T₂ ▷ id₂) ≈⟨ refl⟩∘⟨ ▷id₂ ⟩
      actionʳ ∘ᵥ id₂        ≈⟨ identity₂ʳ ⟩
      actionʳ               ≈⟨ ⟺ identity₂ˡ ⟩
      id₂ ∘ᵥ actionʳ        ∎
  }
  where
    open Monad M₁ renaming (C to C₁; T to T₁)
    open Monad M₂ renaming (C to C₂; T to T₂)
    open Bimodule B
    open Category (hom C₁ C₂)
    open HomReasoning
    open Equiv

bimodule-hom-∘ : {M₁ M₂ : Monad 𝒞} → {B₁ B₂ B₃ : Bimodule M₁ M₂}
                 → Bimodulehomomorphism B₂ B₃ → Bimodulehomomorphism B₁ B₂ → Bimodulehomomorphism B₁ B₃
bimodule-hom-∘ {M₁} {M₂} {B₁} {B₂} {B₃} g f = record
  { α = α g ∘ᵥ α f
  ; linearˡ = begin
      actionˡ₃ ∘ᵥ (α g ∘ᵥ α f) ◁ T₁          ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
      actionˡ₃ ∘ᵥ (α g ◁ T₁) ∘ᵥ (α f ◁ T₁)   ≈⟨ sym-assoc₂ ⟩
      (actionˡ₃ ∘ᵥ (α g ◁ T₁)) ∘ᵥ (α f ◁ T₁) ≈⟨ linearˡ g ⟩∘⟨refl ⟩
      (α g ∘ᵥ actionˡ₂) ∘ᵥ (α f ◁ T₁)        ≈⟨ assoc₂ ⟩
      α g ∘ᵥ actionˡ₂ ∘ᵥ (α f ◁ T₁)          ≈⟨ refl⟩∘⟨ linearˡ f ⟩
      α g ∘ᵥ α f ∘ᵥ actionˡ₁                 ≈⟨ sym-assoc₂ ⟩
      (α g ∘ᵥ α f) ∘ᵥ actionˡ₁               ∎
  ; linearʳ = begin
      actionʳ₃ ∘ᵥ T₂ ▷ (α g ∘ᵥ α f)          ≈⟨ refl⟩∘⟨ (⟺ ∘ᵥ-distr-▷) ⟩
      actionʳ₃ ∘ᵥ (T₂ ▷ α g) ∘ᵥ (T₂ ▷ α f)   ≈⟨ sym-assoc₂ ⟩
      (actionʳ₃ ∘ᵥ (T₂ ▷ α g)) ∘ᵥ (T₂ ▷ α f) ≈⟨ linearʳ g ⟩∘⟨refl ⟩
      (α g ∘ᵥ actionʳ₂) ∘ᵥ (T₂ ▷ α f)        ≈⟨ assoc₂ ⟩
      α g ∘ᵥ actionʳ₂ ∘ᵥ (T₂ ▷ α f)          ≈⟨ refl⟩∘⟨ linearʳ f ⟩
      α g ∘ᵥ α f ∘ᵥ actionʳ₁                 ≈⟨ sym-assoc₂ ⟩
      (α g ∘ᵥ α f) ∘ᵥ actionʳ₁               ∎
  }
  where
    open Bimodulehomomorphism
    open Monad M₁ renaming (C to C₁; T to T₁)
    open Monad M₂ renaming (C to C₂; T to T₂)
    open Bimodule B₁ renaming (F to F₁; actionˡ to actionˡ₁; actionʳ to actionʳ₁)
    open Bimodule B₂ renaming (F to F₂; actionˡ to actionˡ₂; actionʳ to actionʳ₂)
    open Bimodule B₃ renaming (F to F₃; actionˡ to actionˡ₃; actionʳ to actionʳ₃)
    open Category (hom C₁ C₂)
    open HomReasoning
    open Equiv
