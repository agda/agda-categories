{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- GS-monoidal categories, as introduced by Gadducci & Corradini ("gs" for
-- garbage and sharing): symmetric monoidal categories in which every object
-- carries a commutative comonoid structure, coherently with the tensor, and in
-- which neither comonoid map is required to be natural.
--
-- Requiring the comultiplication to be natural yields counital copy categories
-- (Categories.Category.Monoidal.CounitalCopy); requiring both to be natural
-- yields cartesian categories.

module Categories.Category.Monoidal.GSMonoidal
  {o ℓ e} {𝒞 : Category o ℓ e} {monoidal : Monoidal 𝒞} (symmetric : Symmetric monoidal) where

open import Level using (suc; _⊔_)

open import Categories.Object.Monoid using (IsMonoid)

import Categories.Category.Monoidal.Properties
import Categories.Category.Monoidal.Utilities as MonoidalUtils
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Interchange.Braided as BraidedInterchange

record GSMonoidal : Set (suc (o ⊔ ℓ ⊔ e)) where
  open Category 𝒞
  open Symmetric symmetric
  open BraidedProps braided using () renaming (module Shorthands to BraidedShorthands)
  open BraidedShorthands using (σ⇒)
  open BraidedInterchange braided using (module swapInner; swapInner-expand)
  open MonoidalUtils monoidal using (module Shorthands)
  open Shorthands
  open Categories.Category.Monoidal.Properties monoidal using (monoidal-Op)

  field
    isComonoid : ∀ X → IsMonoid (monoidal-Op) X

  Δ : ∀ {X} → X ⇒ X ⊗₀ X
  Δ {X} = IsMonoid.μ (isComonoid X)
  δ : ∀ {X} → X ⇒ unit
  δ {X} = IsMonoid.η (isComonoid X)

  field
    inverse₁ : Δ {unit} ∘ λ⇒ ≈ id
    inverse₂ : λ⇒ ∘ Δ {unit} ≈ id
    cocommutative : ∀ {A} → σ⇒ ∘ Δ ≈ Δ {A}
    preserves : ∀ {X Y} → α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ ((σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒ ∘ (Δ ⊗₁ Δ) ≈ Δ {X ⊗₀ Y}

  -- What `preserves` says: copying a tensor is copying each factor and then
  -- interchanging.  The composite above is the four middle interchange of
  -- Categories.Category.Monoidal.Interchange.Braided, with its two inner
  -- factors composed separately rather than tensored at once, which is the
  -- form a proof of the field wants.

  preserves-interchange : ∀ {X Y} → swapInner.from ∘ (Δ ⊗₁ Δ) ≈ Δ {X ⊗₀ Y}
  preserves-interchange = ∘-resp-≈ˡ swapInner-expand ○ assoc ○ ∘-resp-≈ʳ assoc
                        ○ ∘-resp-≈ʳ (∘-resp-≈ʳ assoc) ○ preserves
    where open HomReasoning

  module _ {X : Obj} where
    open IsMonoid (isComonoid X) hiding (μ; η) renaming (assoc to Δ-assoc; identityˡ to δ-identityˡ; identityʳ to δ-identityʳ) public
