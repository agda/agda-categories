{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory

module Categories.Bicategory.Monad.Bimodule {o ℓ e t} {𝒞 : Bicategory o ℓ e t} where

open import Level
open import Categories.Bicategory.Monad using (Monad)
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open Shorthands

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

record Bimodulehomomorphism {M₁ M₂ : Monad 𝒞} (B₁ B₂ : Bimodule M₁ M₂) : Set (ℓ ⊔ e) where
  open Monad using (T)
  open Bimodule using (F; actionˡ; actionʳ)
  field
    α       : F B₁ ⇒₂ F B₂
    linearˡ : actionˡ B₂ ∘ᵥ (α ◁ T M₁) ≈ α ∘ᵥ actionˡ B₁
    linearʳ : actionʳ B₂ ∘ᵥ (T M₂ ▷ α) ≈ α ∘ᵥ actionʳ B₁

id-bimodule-hom : {M₁ M₂ : Monad 𝒞} → {B : Bimodule M₁ M₂} → Bimodulehomomorphism B B
id-bimodule-hom {M₁} {M₂} {B} = record
  { α = id₂
  ; linearˡ = id-linearˡ
  ; linearʳ = id-linearʳ
  }
  where
    open Monad using (C; T)
    open Bimodule B using (actionˡ; actionʳ)
    open hom.HomReasoning

    id-linearˡ : actionˡ ∘ᵥ (id₂ ◁ T M₁) ≈ id₂ ∘ᵥ actionˡ
    id-linearˡ = begin
      actionˡ ∘ᵥ (id₂ ◁ T M₁) ≈⟨ refl⟩∘⟨ id₂◁ ⟩
      actionˡ ∘ᵥ id₂          ≈⟨ identity₂ʳ ⟩
      actionˡ                 ≈⟨ ⟺ identity₂ˡ ⟩
      id₂ ∘ᵥ actionˡ          ∎

    id-linearʳ : actionʳ ∘ᵥ (T M₂ ▷ id₂) ≈ id₂ ∘ᵥ actionʳ
    id-linearʳ = begin
      actionʳ ∘ᵥ (T M₂ ▷ id₂) ≈⟨ refl⟩∘⟨ ▷id₂ ⟩
      actionʳ ∘ᵥ id₂          ≈⟨ identity₂ʳ ⟩
      actionʳ                 ≈⟨ ⟺ identity₂ˡ ⟩
      id₂ ∘ᵥ actionʳ          ∎

bimodule-hom-∘ : {M₁ M₂ : Monad 𝒞} → {B₁ B₂ B₃ : Bimodule M₁ M₂}
               → Bimodulehomomorphism B₂ B₃ → Bimodulehomomorphism B₁ B₂ → Bimodulehomomorphism B₁ B₃
bimodule-hom-∘ {M₁} {M₂} {B₁} {B₂} {B₃} g f = record
  { α = α g ∘ᵥ α f
  ; linearˡ = g∘f-linearˡ
  ; linearʳ = g∘f-linearʳ
  }
  where
    open Bimodulehomomorphism using (α; linearˡ; linearʳ)
    open Monad using (C; T)
    open Bimodule using (F; actionˡ; actionʳ)
    open hom.HomReasoning

    g∘f-linearˡ : actionˡ B₃ ∘ᵥ (α g ∘ᵥ α f) ◁ T M₁ ≈ (α g ∘ᵥ α f) ∘ᵥ actionˡ B₁
    g∘f-linearˡ = begin
      actionˡ B₃ ∘ᵥ (α g ∘ᵥ α f) ◁ T M₁            ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
      actionˡ B₃ ∘ᵥ (α g ◁ T M₁) ∘ᵥ (α f ◁ T M₁)   ≈⟨ sym-assoc₂ ⟩
      (actionˡ B₃ ∘ᵥ (α g ◁ T M₁)) ∘ᵥ (α f ◁ T M₁) ≈⟨ linearˡ g ⟩∘⟨refl ⟩
      (α g ∘ᵥ actionˡ B₂) ∘ᵥ (α f ◁ T M₁)          ≈⟨ assoc₂ ⟩
      α g ∘ᵥ actionˡ B₂ ∘ᵥ (α f ◁ T M₁)            ≈⟨ refl⟩∘⟨ linearˡ f ⟩
      α g ∘ᵥ α f ∘ᵥ actionˡ B₁                     ≈⟨ sym-assoc₂ ⟩
      (α g ∘ᵥ α f) ∘ᵥ actionˡ B₁                   ∎

    g∘f-linearʳ : actionʳ B₃ ∘ᵥ T M₂ ▷ (α g ∘ᵥ α f) ≈ (α g ∘ᵥ α f) ∘ᵥ actionʳ B₁
    g∘f-linearʳ = begin
      actionʳ B₃ ∘ᵥ T M₂ ▷ (α g ∘ᵥ α f)            ≈⟨ refl⟩∘⟨ (⟺ ∘ᵥ-distr-▷) ⟩
      actionʳ B₃ ∘ᵥ (T M₂ ▷ α g) ∘ᵥ (T M₂ ▷ α f)   ≈⟨ sym-assoc₂ ⟩
      (actionʳ B₃ ∘ᵥ (T M₂ ▷ α g)) ∘ᵥ (T M₂ ▷ α f) ≈⟨ linearʳ g ⟩∘⟨refl ⟩
      (α g ∘ᵥ actionʳ B₂) ∘ᵥ (T M₂ ▷ α f)          ≈⟨ assoc₂ ⟩
      α g ∘ᵥ actionʳ B₂ ∘ᵥ (T M₂ ▷ α f)            ≈⟨ refl⟩∘⟨ linearʳ f ⟩
      α g ∘ᵥ α f ∘ᵥ actionʳ B₁                     ≈⟨ sym-assoc₂ ⟩
      (α g ∘ᵥ α f) ∘ᵥ actionʳ B₁                   ∎
