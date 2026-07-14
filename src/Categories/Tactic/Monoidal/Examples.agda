{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Tactic.Monoidal.Examples
  {o ℓ e a : Level}
  {𝒞 : Category o ℓ e}
  (M : Monoidal 𝒞)
  {Atom : Set a}
  (⟦_⟧ₐ : Atom → Category.Obj 𝒞)
  (w x y z : Atom)
  where

open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Tactic.Monoidal.Core M ⟦_⟧ₐ
open import Categories.Tactic.Monoidal using (solve₀; solveMonoidal)

open import Categories.Morphism 𝒞 using (_≅_)
open Category 𝒞 hiding (_⇒_)
open Monoidal M hiding (⊗) renaming (_⊗₁_ to _⊗₁ᶜ_)
open Free Atom renaming (_∘_ to _∘ᶠ_)

private
  assoc-iso : ⟦ (‹ w › ⊗ ‹ x ›) ⊗ ‹ y › ⟧₀ ≅ ⟦ ‹ w › ⊗ (‹ x › ⊗ ‹ y ›) ⟧₀
  assoc-iso = object-coherence {X = (‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›}
                               {Y = ‹ w › ⊗ (‹ x › ⊗ ‹ y ›)} refl

  assoc-iso-solved : ⟦ (‹ w › ⊗ ‹ x ›) ⊗ ‹ y › ⟧₀ ≅ ⟦ ‹ w › ⊗ (‹ x › ⊗ ‹ y ›) ⟧₀
  assoc-iso-solved = solve₀ M ⟦_⟧ₐ

  unit-iso : ⟦ (I ⊗ ‹ w ›) ⊗ (‹ x › ⊗ I) ⟧₀ ≅ ⟦ ‹ w › ⊗ ‹ x › ⟧₀
  unit-iso = object-coherence {X = (I ⊗ ‹ w ›) ⊗ (‹ x › ⊗ I)}
                              {Y = ‹ w › ⊗ ‹ x ›} refl

  unit-iso-solved : ⟦ (I ⊗ ‹ w ›) ⊗ (‹ x › ⊗ I) ⟧₀ ≅ ⟦ ‹ w › ⊗ ‹ x › ⟧₀
  unit-iso-solved = solve₀ M ⟦_⟧ₐ

  reassoc-cancel
    : ⟦ α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⟧₁
      ≈ ⟦ idₘ {(‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›} ⟧₁
  reassoc-cancel =
    coherence-from-loop {f = α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›}} {g = idₘ}
      (Equiv.trans identityˡ associator.isoˡ)

  triangle-faithful
    : ⟦ (idₘ ⊗₁ λ⇒) ∘ᶠ α⇒ {‹ w ›} {I} {‹ x ›} ⟧₁
      ≈ ⟦ ρ⇒ {‹ w ›} ⊗₁ idₘ {‹ x ›} ⟧₁
  triangle-faithful = triangle

  pentagon-faithful
    : ⟦ (idₘ ⊗₁ α⇒) ∘ᶠ
        (α⇒ ∘ᶠ (α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⊗₁ idₘ {‹ z ›})) ⟧₁
      ≈ ⟦ α⇒ ∘ᶠ α⇒ {‹ w › ⊗ ‹ x ›} {‹ y ›} {‹ z ›} ⟧₁
  pentagon-faithful = pentagon

  reassoc-cancel-goal : Set e
  reassoc-cancel-goal =
    ⟦ α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⟧₁
    ≈ ⟦ idₘ {(‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›} ⟧₁

  reassoc-cancel-solved
    : ⟦ α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⟧₁
      ≈ ⟦ idₘ {(‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›} ⟧₁
  reassoc-cancel-solved = solveMonoidal M ⟦_⟧ₐ
