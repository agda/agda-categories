{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using () renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Enriched.Category using (Category)

-- Derived unit laws for generalized elements of enriched hom-objects.

module Categories.Enriched.Category.Properties
  {o ℓ e v} {V : Setoid-Category o ℓ e} (M : Monoidal V) (C : Category M v) where

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)
open import Categories.Morphism.Reasoning V

open Setoid-Category V renaming (id to idV)
  using (_⇒_; _≈_; _∘_; assoc; sym-assoc; identityˡ; identityʳ)
open Monoidal M using (_⊗₀_; _⊗₁_; unit; module unitorˡ; module unitorʳ;
  unitorˡ-commute-from; unitorʳ-commute-from)
open Category C
open Shorthands

private
  variable
    A B : Obj
    X : Setoid-Category.Obj V
    f g : X ⇒ hom A B

abstract
  unitˡ-var : ⊚ ∘ (id ⊗₁ f) ∘ λ⇐ ≈ f
  unitˡ-var {f = f} = begin
    ⊚ ∘ (id ⊗₁ f) ∘ λ⇐                        ≈⟨ pushʳ (⟺ (identityʳ ⟩⊗⟨ identityˡ) ⟩∘⟨refl) ⟩
    (⊚ ∘ ((id ∘ idV) ⊗₁ (idV ∘ f))) ∘ λ⇐      ≈⟨ pushʳ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
    ((⊚ ∘ (id ⊗₁ idV)) ∘ (idV ⊗₁ f)) ∘ λ⇐     ≈⟨ unitˡ ⟩∘⟨refl ⟩∘⟨refl ⟩
    (λ⇒ ∘ (idV ⊗₁ f)) ∘ λ⇐                    ≈⟨ unitorˡ-commute-from ⟩∘⟨refl ⟩
    (f ∘ λ⇒) ∘ λ⇐                             ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
    f                                         ∎

  unitʳ-var : ⊚ ∘ (f ⊗₁ id) ∘ ρ⇐ ≈ f
  unitʳ-var {f = f} = begin
    ⊚ ∘ (f ⊗₁ id) ∘ ρ⇐                        ≈⟨ pushʳ (⟺ (identityˡ ⟩⊗⟨ identityʳ) ⟩∘⟨refl) ⟩
    (⊚ ∘ ((idV ∘ f) ⊗₁ (id ∘ idV))) ∘ ρ⇐      ≈⟨ pushʳ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
    ((⊚ ∘ (idV ⊗₁ id)) ∘ (f ⊗₁ idV)) ∘ ρ⇐     ≈⟨ unitʳ ⟩∘⟨refl ⟩∘⟨refl ⟩
    (ρ⇒ ∘ (f ⊗₁ idV)) ∘ ρ⇐                    ≈⟨ unitorʳ-commute-from ⟩∘⟨refl ⟩
    (f ∘ ρ⇒) ∘ ρ⇐                             ≈⟨ cancelʳ unitorʳ.isoʳ ⟩
    f                                         ∎

  id-commuteˡ : f ≈ g → ⊚ ∘ (id ⊗₁ f) ∘ λ⇐ ≈ ⊚ ∘ (g ⊗₁ id) ∘ ρ⇐
  id-commuteˡ f≈g = unitˡ-var ○ f≈g ○ ⟺ unitʳ-var

  id-commuteʳ : f ≈ g → ⊚ ∘ (id ⊗₁ g) ∘ λ⇐ ≈ ⊚ ∘ (f ⊗₁ id) ∘ ρ⇐
  id-commuteʳ f≈g = unitˡ-var ○ ⟺ f≈g ○ ⟺ unitʳ-var
