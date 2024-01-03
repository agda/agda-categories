------------------------------------------------------------------------
-- The Agda categories library
--
-- Lists where all elements satisfy a given property, biases towards
-- lookup. This is akin to Data.Vec.Functional.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.All.Functional where

open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Wrap using (Wrap)
open import Level using (_⊔_)
open import Relation.Binary.Core using (Rel)

All : ∀ {o ℓ} {X : Set o} (V : X → Set ℓ) (Δ : List X) → Set (o ⊔ ℓ)
All V Δ = ∀ {y} → y ∈ Δ → V y

-- Pointwise lifting of a binary relation from values to All.

infix 4 [_]_∼_
[_]_∼_ : ∀ {o ℓ e} {X : Set o} {V : X → Set ℓ} {Δ : List X} →
  (∀ {x} → Rel (V x) e) → Rel (All V Δ) (o ⊔ e)
[_]_∼_ = Wrap λ _≈_ ρ σ → ∀ {y} (i : y ∈ _) → ρ i ≈ σ i
