{-# OPTIONS --without-K --safe #-}

import Categories.Category.Core as Base
open import Categories.Category.Monoidal.Core using (Monoidal)

-- The scalar enriched category is the unit for tensor products of enriched
-- categories.

module Categories.Enriched.Category.Scalar
  {o ℓ e} {V : Base.Category o ℓ e} (M : Monoidal V) where

open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level)

open import Categories.Category.Monoidal.Properties M using (coherence₁; coherence₃)
open import Categories.Category.Monoidal.Utilities M
  using (unitor-coherenceˡ; module Shorthands)
import Categories.Enriched.Category M as Enriched
open import Categories.Morphism.Reasoning V

open Base.Category V
open HomReasoning
open Monoidal M using (unit; _⊗₁_; module ⊗)
open Shorthands

private
  variable
    v : Level

V-Scalar : Enriched.Category v
V-Scalar = record
  { Obj = ⊤
  ; hom = λ _ _ → unit
  ; id = id
  ; ⊚ = λ⇒
  ; ⊚-assoc = begin
      λ⇒ ∘ (λ⇒ ⊗₁ id)                  ≈˘⟨ refl⟩∘⟨ coherence₁ ⟩
      λ⇒ ∘ λ⇒ ∘ α⇒                    ≈˘⟨ refl⟩∘⟨ unitor-coherenceˡ ⟩∘⟨refl ⟩
      λ⇒ ∘ (id ⊗₁ λ⇒) ∘ α⇒            ∎
  ; unitˡ = elimʳ ⊗.identity
  ; unitʳ = elimʳ ⊗.identity ○ coherence₃
  }
