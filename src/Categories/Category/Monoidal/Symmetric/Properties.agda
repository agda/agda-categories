{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Category.Monoidal.Symmetric.Properties
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (SM : Symmetric M) where

import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
import Categories.Category.Construction.Core C as Core
import Categories.Category.Monoidal.Utilities M as MonUtil

open import Categories.Category.Monoidal.Properties M using (monoidal-Op)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Morphism C using (_≅_)
open import Categories.Morphism.Reasoning C
open import Data.Product using (_,_)

open Category C
open Symmetric SM

-- Shorthands for the braiding

open BraidedProperties braided public using (module Shorthands)
open BraidedProperties braided using (braiding-coherence-inv)
  renaming (braiding-coherence′ to bc′)
open Shorthands
open Core.Shorthands using (idᵢ)
open MonUtil using (_⊗ᵢ_)
open MonUtil.Shorthands

-- Extra properties of the braiding in a symmetric monoidal category

braiding-selfInverse : ∀ {X Y} → braiding.⇐.η (X , Y) ≈ braiding.⇒.η (Y , X)
braiding-selfInverse = introʳ commutative ○ cancelˡ (braiding.iso.isoˡ _)

inv-commutative : ∀ {X Y} → braiding.⇐.η (X , Y) ∘ braiding.⇐.η (Y , X) ≈ id
inv-commutative = ∘-resp-≈ braiding-selfInverse braiding-selfInverse ○ commutative

mirrorˡ : ∀ {X Y Z} → (id {X} ⊗₁ σ⇒ {Z} {Y}) ∘ σ⇐ {X} {Z ⊗₀ Y} ≈ σ⇒ ∘ (σ⇒ ⊗₁ id)
mirrorˡ = begin
  id ⊗₁ σ⇒ ∘ σ⇐         ≈⟨ refl⟩∘⟨ braiding-selfInverse ⟩
  id ⊗₁ σ⇒ ∘ σ⇒         ≈˘⟨ σ⇒-comm ⟩
  σ⇒ ∘ σ⇒ ⊗₁ id         ∎

mirrorʳ : ∀ {X Y Z} → (σ⇒ {Z} {Y} ⊗₁ id {X}) ∘ σ⇐ {Z ⊗₀ Y} {X} ≈ σ⇒ ∘ (id ⊗₁ σ⇒)
mirrorʳ = begin
  σ⇒ ⊗₁ id ∘ σ⇐         ≈⟨ refl⟩∘⟨ braiding-selfInverse ⟩
  σ⇒ ⊗₁ id ∘ σ⇒         ≈˘⟨ σ⇒-comm ⟩
  σ⇒ ∘ id ⊗₁ σ⇒         ∎

cup-swap : ∀ {A X} {cup : unit ⇒ X} →
  (id {A} ⊗₁ cup) ∘ ρ⇐ ≈ σ⇐ ∘ (cup ⊗₁ id) ∘ λ⇐
cup-swap {cup = cup} = begin
  id ⊗₁ cup ∘ ρ⇐       ≈⟨ refl⟩∘⟨ ⟺ braiding-coherence-inv ⟩
  id ⊗₁ cup ∘ σ⇐ ∘ λ⇐  ≈⟨ extendʳ (⟺ σ⇐-comm) ⟩
  σ⇐ ∘ cup ⊗₁ id ∘ λ⇐  ∎

middle-braid : ∀ {Y A Z} →
  (α⇒ {Y} {A} {Z} ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ σ⇐
  ≈ (id ⊗₁ σ⇒) ∘ α⇒
middle-braid = begin
  (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ σ⇐                             ≈⟨ introˡ (_≅_.isoˡ (idᵢ ⊗ᵢ braided-iso)) ⟩
  ((id ⊗₁ σ⇒) ∘ (id ⊗₁ σ⇒)) ∘ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ σ⇐   ≈⟨ refl⟩∘⟨ assoc²βγ ⟩
  ((id ⊗₁ σ⇒) ∘ (id ⊗₁ σ⇒)) ∘ (α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐ ∘ σ⇐   ≈⟨ extend² hexagon₁ ⟩
  ((id ⊗₁ σ⇒) ∘ α⇒) ∘ (σ⇒ ∘ α⇒) ∘ (α⇐ ∘ σ⇐)               ≈⟨ refl⟩∘⟨ cancelInner associator.isoʳ ⟩
  ((id ⊗₁ σ⇒) ∘ α⇒) ∘ σ⇒ ∘ σ⇐                             ≈⟨ elimʳ (braiding.iso.isoʳ _) ⟩
  (id ⊗₁ σ⇒) ∘ α⇒                                         ∎

-- The opposite monoidal category is symmetric

open BraidedProperties braided using (braided-Op)

symmetric-Op : Symmetric monoidal-Op
symmetric-Op = record
    { braided = braided-Op
    ; commutative = inv-commutative
    }

-- Cyclically rotate three tensor factors.
module Rotation where
  private
    variable
      X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Obj
      f : X₁ ⇒ X₂
      g : Y₁ ⇒ Y₂
      h : Z₁ ⇒ Z₂

  cycle : (X₁ ⊗₀ Y₁) ⊗₀ Z₁ ⇒ Y₁ ⊗₀ (Z₁ ⊗₀ X₁)
  cycle = (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)

  cycle-natural : cycle ∘ ((f ⊗₁ g) ⊗₁ h) ≈ (g ⊗₁ (h ⊗₁ f)) ∘ cycle
  cycle-natural {f = f} {g = g} {h = h} = begin
    cycle ∘ ((f ⊗₁ g) ⊗₁ h)                         ≈⟨ pullʳ (glue assoc-commute-from cycle-head) ⟩
    (id ⊗₁ σ⇒) ∘ (g ⊗₁ (f ⊗₁ h)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)  ≈⟨ extendʳ cycle-tail ⟩
    (g ⊗₁ (h ⊗₁ f)) ∘ cycle                         ∎
    where
      cycle-head = parallel σ⇒-comm id-comm-sym
      cycle-tail = parallel id-comm-sym σ⇒-comm

  cycle-cancel : cycle {Y₁} {X₁} {Z₁} ∘ (σ⇒ ⊗₁ id) ≈ (id ⊗₁ σ⇒) ∘ α⇒
  cycle-cancel = begin
    cycle ∘ (σ⇒ ⊗₁ id)  ≈⟨ pullʳ (cancelʳ (⊗-cancel commutative identity²)) ⟩
    (id ⊗₁ σ⇒) ∘ α⇒     ∎

  cycle-unit : (id ⊗₁ ρ⇒) ∘ cycle ∘ (λ⇐ ⊗₁ id) ≈ id {X₁ ⊗₀ Y₁}
  cycle-unit = begin
    (id ⊗₁ ρ⇒) ∘ cycle ∘ (λ⇐ ⊗₁ id)                     ≈⟨ pullˡ (pullˡ merge₂ˡ) ⟩
    ((id ⊗₁ (ρ⇒ ∘ σ⇒)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ (λ⇐ ⊗₁ id)  ≈⟨ refl⟩⊗⟨ bc′ ⟩∘⟨refl ⟩∘⟨refl ⟩
    ((id ⊗₁ λ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ (λ⇐ ⊗₁ id)         ≈⟨ pullˡ triangle ⟩∘⟨refl ⟩
    ((ρ⇒ ⊗₁ id) ∘ (σ⇒ ⊗₁ id)) ∘ (λ⇐ ⊗₁ id)              ≈⟨ merge₁ˡ ⟩∘⟨refl ⟩
    ((ρ⇒ ∘ σ⇒) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)                      ≈⟨ bc′ ⟩⊗⟨refl ⟩∘⟨refl ⟩
    (λ⇒ ⊗₁ id) ∘ (λ⇐ ⊗₁ id)                             ≈⟨ ⊗-cancel unitorˡ.isoʳ identity² ⟩
    id                                                  ∎

open Rotation public
