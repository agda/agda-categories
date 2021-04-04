{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (module Commutation)
  renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Enriched.Category.Opposite
  {o ℓ e} {V : Setoid-Category o ℓ e} {M : Monoidal V} (S : Symmetric M) where

-- The dual of a V-enriched category.
--
-- Note that, for this construction to work, V needs to be a
-- *symmetric* monoidal category.

open import Data.Product using (_,_)

import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)
open import Categories.Enriched.Category M using (Category)
open import Categories.Morphism.Reasoning V

open Setoid-Category V renaming (id to idV) using (_⇒_; _∘_; assoc)
open Commutation V
open Shorthands
open Symmetric S
open BraidedProperties (Symmetric.braided S) using (braiding-coherence)

private σ = λ {A B} → braiding.⇒.η (A , B)

-- The opposite of a V-enriched category.

op : ∀ {v} → Category v → Category v
op C = record
  { Obj = Obj
  ; hom = λ A B → hom B A
  ; id  = id
  ; ⊚   = ⊚ ∘ σ
  ; ⊚-assoc = begin
      (⊚ ∘ σ) ∘ (⊚ ∘ σ) ⊗₁ idV               ≈⟨ refl⟩∘⟨ split₁ʳ ⟩
      (⊚ ∘ σ) ∘ ⊚ ⊗₁ idV ∘ σ ⊗₁ idV          ≈⟨ extend² (braiding.⇒.commute _) ⟩
      (⊚ ∘ idV ⊗₁ ⊚) ∘ σ ∘ σ ⊗₁ idV          ≈⟨ ⊚-assoc′ ⟩∘⟨refl ⟩
      (⊚ ∘ ⊚ ⊗₁ idV ∘ α⇐) ∘ σ ∘ σ ⊗₁ idV     ≈˘⟨ assoc ⟩∘⟨refl ⟩
      ((⊚ ∘ ⊚ ⊗₁ idV) ∘ α⇐) ∘ σ ∘ σ ⊗₁ idV   ≈⟨ pullʳ invert-braidings ⟩
      (⊚ ∘ ⊚ ⊗₁ idV) ∘ σ ∘ idV ⊗₁ σ ∘ α⇒     ≈˘⟨ refl⟩∘⟨ assoc ⟩
      (⊚ ∘ ⊚ ⊗₁ idV) ∘ (σ ∘ idV ⊗₁ σ) ∘ α⇒
                                    ≈˘⟨ pushˡ (extend² (braiding.⇒.commute _)) ⟩
      ((⊚ ∘ σ) ∘ idV ⊗₁ ⊚ ∘ idV ⊗₁ σ) ∘ α⇒   ≈˘⟨ pullˡ (refl⟩∘⟨ split₂ʳ) ⟩
      (⊚ ∘ σ) ∘ idV ⊗₁ (⊚ ∘ σ) ∘ α⇒   ∎
  ; unitˡ = λ {A B} → begin
      (⊚ ∘ σ) ∘ id ⊗₁ idV   ≈⟨ pullʳ (braiding.⇒.commute _) ⟩
      ⊚ ∘ idV ⊗₁ id ∘ σ     ≈⟨ pullˡ unitʳ ⟩
      ρ⇒ ∘ σ                ≈˘⟨ switch-fromtoʳ braided-iso braiding-coherence ⟩
      λ⇒                    ∎
  ; unitʳ = begin
      (⊚ ∘ σ) ∘ idV ⊗₁ id   ≈⟨ pullʳ (braiding.⇒.commute _) ⟩
      ⊚ ∘ id ⊗₁ idV ∘ σ     ≈⟨ pullˡ unitˡ ⟩
      λ⇒ ∘ σ                ≈⟨ braiding-coherence ⟩
      ρ⇒                    ∎
  }
  where
    open Category C

    ⊚-assoc′ : ∀ {A B C D} →
               [ hom C D ⊗₀ (hom B C ⊗₀ hom A B) ⇒ hom A D ]⟨
                 idV ⊗₁ ⊚    ⇒⟨ hom C D ⊗₀ hom A C ⟩
                 ⊚
               ≈ α⇐          ⇒⟨ (hom C D ⊗₀ hom B C) ⊗₀ hom A B ⟩
                 ⊚ ⊗₁ idV    ⇒⟨ hom B D ⊗₀ hom A B ⟩
                 ⊚
               ⟩
    ⊚-assoc′ = switch-fromtoʳ associator (assoc ○ ⟺ ⊚-assoc) ○ assoc

    -- implements the following equation of string diagrams
    --
    --     |   |   |               |   |   |
    --      \ /    |               |    \ /
    --       \     |               |     \
    --      / \   /                 \   / \
    --     |   \ /        ===        \ /   |
    --      \   \                     /   /
    --       \ / \                   / \ /
    --        \   \                 /   /
    --       / \   \               /   / \
    --      |   |   |             |   |   |
    --
    invert-braidings : ∀ {A B C} →
                       [ (A ⊗₀ B) ⊗₀ C ⇒ (C ⊗₀ B) ⊗₀ A ]⟨
                         σ ⊗₁ idV      ⇒⟨ (B ⊗₀ A) ⊗₀ C ⟩
                         σ             ⇒⟨ C ⊗₀ (B ⊗₀ A) ⟩
                         α⇐
                       ≈ α⇒            ⇒⟨ A ⊗₀ (B ⊗₀ C) ⟩
                         idV ⊗₁ σ      ⇒⟨ A ⊗₀ (C ⊗₀ B) ⟩
                         σ
                       ⟩
    invert-braidings = begin
        α⇐ ∘ σ ∘ σ ⊗₁ idV
      ≈⟨ extendʳ (switch-tofromʳ associator (⟺ hexagon₂)) ⟩
        ((σ ⊗₁ idV ∘ α⇐) ∘ idV ⊗₁ σ) ∘ α⇒ ∘ σ ⊗₁ idV
      ≈⟨ assoc ⟩
        (σ ⊗₁ idV ∘ α⇐) ∘ idV ⊗₁ σ ∘ α⇒ ∘ σ ⊗₁ idV
      ≈˘⟨ pushʳ (switch-fromtoˡ associator (⟺ hexagon₁)) ⟩
        σ ⊗₁ idV ∘ σ ∘ α⇒
      ≈˘⟨ extendʳ (braiding.⇒.commute _) ⟩
        σ ∘ idV ⊗₁ σ ∘ α⇒
      ∎
