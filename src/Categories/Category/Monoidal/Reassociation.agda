{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal.Core using (Monoidal)

-- Reassociation lemmas for monoidal categories.

module Categories.Category.Monoidal.Reassociation
  {o ℓ e} {𝒞 : Category o ℓ e} (M : Monoidal 𝒞) where

open Category 𝒞
open Monoidal M

open import Categories.Category.Construction.Core 𝒞 as Core using (Core)
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.Reasoning M
import Categories.Morphism.Reasoning as MR

open Core.Shorthands
open Shorthands
open MR 𝒞

private
  variable
    A B C D : Obj

pentagon-assoc
  : α⇒ {A ⊗₀ B} {C} {D} ∘ (α⇐ {A} {B} {C} ⊗₁ id) ∘ α⇐ {A} {B ⊗₀ C} {D}
    ≈ α⇐ {A} {B} {C ⊗₀ D} ∘ (id ⊗₁ α⇒ {B} {C} {D})
pentagon-assoc = begin
  α⇒ ∘ (α⇐ ⊗₁ id) ∘ α⇐                                 ≈⟨ refl⟩∘⟨ insertʳ (⊗-cancel identity² associator.isoˡ) ⟩
  α⇒ ∘ (((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ α⇒)   ≈⟨ refl⟩∘⟨ pentagon-inv ⟩∘⟨refl ⟩
  α⇒ ∘ (α⇐ ∘ α⇐) ∘ (id ⊗₁ α⇒)                          ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ α⇐ ∘ α⇐ ∘ (id ⊗₁ α⇒)                            ≈⟨ cancelˡ associator.isoʳ ⟩
  α⇐ ∘ (id ⊗₁ α⇒)                                      ∎

λ⇒-assoc : (λ⇒ {A} ⊗₁ id {B}) ∘ α⇐ {unit} {A} {B} ≈ λ⇒
λ⇒-assoc = ⟺ (switch-fromtoʳ associator coherence₁)

λ⇐-assoc : α⇒ ∘ (λ⇐ {A} ⊗₁ id {B}) ≈ λ⇐
λ⇐-assoc = begin
  α⇒ ∘ (λ⇐ ⊗₁ id)   ≈⟨ refl⟩∘⟨ ⟺ coherence-inv₁ ⟩
  α⇒ ∘ (α⇐ ∘ λ⇐)    ≈⟨ cancelˡ associator.isoʳ ⟩
  λ⇐                ∎

ρ⇒-assoc : ρ⇒ ∘ α⇐ {A} {B} {unit} ≈ id {A} ⊗₁ ρ⇒
ρ⇒-assoc = ⟺ (switch-fromtoʳ associator coherence₂)

ρ⇐-assoc : id {A} ⊗₁ ρ⇐ {B} ≈ α⇒ ∘ ρ⇐ {A ⊗₀ B}
ρ⇐-assoc = begin
  id ⊗₁ ρ⇐                 ≈˘⟨ cancelˡ associator.isoʳ ⟩
  α⇒ ∘ (α⇐ ∘ (id ⊗₁ ρ⇐))   ≈⟨ refl⟩∘⟨ coherence-inv₂ ⟩
  α⇒ ∘ ρ⇐                  ∎
