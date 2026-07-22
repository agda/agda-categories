{-# OPTIONS --without-K --safe #-}

-- Consequences of the trace in a traced monoidal category:
--   * the trace commutes with the left and right scalar actions, and those two
--     actions agree on it (scalars are central);
--   * the trace of an endomorphism `f : X ⇒ X`, closed up with the unitors, is a
--     scalar, and the trace of `id {X}` is the dimension of `X`;
--   * the trace transports to the opposite monoidal category.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Traced using (Traced)

module Categories.Category.Monoidal.Traced.Properties
    {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (T : Traced M) where

open Category C
open Traced T

open import Categories.Category.Monoidal.Scalars M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Morphism.Reasoning C
open import Categories.Category.Monoidal.Reassociation M
  using (λ⇒-assoc; λ⇐-assoc; α⇐-⊗id-commute)
open import Categories.Category.Monoidal.Properties M using (monoidal-Op)
open import Categories.Category.Monoidal.Braided.Properties braided
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Symmetric.Properties symmetric
  using (symmetric-Op; braiding-selfInverse)
import Categories.Category.Monoidal.Utilities M as MonUtil
open MonUtil.Shorthands
open BraidShorthands

private
  variable
    A B X Y : Obj
    s : Scalar
    f : A ⇒ B
    ff : A ⊗₀ X ⇒ B ⊗₀ X

------------------------------------------------------------------------------
-- Scalar actions and the trace.

private
  -- The left action is post-composition by the endomorphism `s ·ˡ id`: it is a
  -- monoid action, so it splits `s ·ˡ f` as `(s ·ₛ idₛ) ·ˡ (id ∘ f)`.
  ·ˡ-natural : s ·ˡ f ≈ (s ·ˡ id) ∘ f
  ·ˡ-natural {s = s} {f = f} = begin
    s ·ˡ f                   ≈⟨ ·ˡ-resp-≈ (⟺ identityʳ) (⟺ identityˡ) ⟩
    (s ·ₛ idₛ) ·ˡ (id ∘ f)   ≈⟨ ·ˡ-∘ ⟩
    (s ·ˡ id) ∘ (idₛ ·ˡ f)   ≈⟨ refl⟩∘⟨ id-·ˡ ⟩
    (s ·ˡ id) ∘ f            ∎

  -- Conjugating a left whisker by the associator pushes it one factor down.
  α-conjugate : {g : A ⇒ B} → α⇐ ∘ (g ⊗₁ id {X ⊗₀ Y}) ∘ α⇒ ≈ (g ⊗₁ id) ⊗₁ id
  α-conjugate = pullˡ α⇐-⊗id-commute ○ cancelʳ associator.isoˡ

  -- The left action on `id` over a tensor only touches the left factor: split
  -- both unitors off the associator, conjugate the scalar's whisker down onto
  -- the left factor, then merge the whiskers back together.
  ·ˡ-id⊗ : s ·ˡ id {A ⊗₀ X} ≈ (s ·ˡ id) ⊗₁ id
  ·ˡ-id⊗ {s = s} = begin
    λ⇒ ∘ (s ⊗₁ id) ∘ λ⇐                              ≈˘⟨ λ⇒-assoc ⟩∘⟨ refl⟩∘⟨ λ⇐-assoc ⟩
    ((λ⇒ ⊗₁ id) ∘ α⇐) ∘ (s ⊗₁ id) ∘ α⇒ ∘ (λ⇐ ⊗₁ id)  ≈⟨ assoc ○ (refl⟩∘⟨ assoc²εβ) ⟩
    (λ⇒ ⊗₁ id) ∘ (α⇐ ∘ (s ⊗₁ id) ∘ α⇒) ∘ (λ⇐ ⊗₁ id)  ≈⟨ refl⟩∘⟨ α-conjugate ⟩∘⟨refl ⟩
    (λ⇒ ⊗₁ id) ∘ ((s ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)      ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
    (λ⇒ ⊗₁ id) ∘ ((s ⊗₁ id) ∘ λ⇐) ⊗₁ id              ≈⟨ merge₁ˡ ⟩
    (λ⇒ ∘ (s ⊗₁ id) ∘ λ⇐) ⊗₁ id                      ∎

-- Pull a left scalar out of the trace: the scalar rides the free wire.
trace-resp-scalarˡ : trace (s ·ˡ ff) ≈ s ·ˡ trace ff
trace-resp-scalarˡ {s = s} {ff = ff} = begin
  trace (s ·ˡ ff)                ≈⟨ trace-resp-≈ ·ˡ-natural ⟩
  trace ((s ·ˡ id) ∘ ff)         ≈⟨ trace-resp-≈ (·ˡ-id⊗ ⟩∘⟨refl) ⟩
  trace (((s ·ˡ id) ⊗₁ id) ∘ ff) ≈⟨ tightenₗ ⟩
  (s ·ˡ id) ∘ trace ff           ≈˘⟨ ·ˡ-natural ⟩
  s ·ˡ trace ff                  ∎

trace-scalar-idˡ : trace (idₛ ·ˡ ff) ≈ trace ff
trace-scalar-idˡ = trace-resp-≈ id-·ˡ

-- Pull a right scalar out of the trace, by reducing to the left case.
-- (`scalar-central : f ·ʳ s ≈ s ·ˡ f`, that the two actions agree, comes from
-- `Braided.Properties`.)
trace-resp-scalarʳ : trace (ff ·ʳ s) ≈ trace ff ·ʳ s
trace-resp-scalarʳ {ff = ff} {s = s} = begin
  trace (ff ·ʳ s)  ≈⟨ trace-resp-≈ scalar-central ⟩
  trace (s ·ˡ ff)  ≈⟨ trace-resp-scalarˡ ⟩
  s ·ˡ trace ff    ≈˘⟨ scalar-central ⟩
  trace ff ·ʳ s    ∎

trace-scalar-idʳ : trace (ff ·ʳ idₛ) ≈ trace ff
trace-scalar-idʳ = trace-resp-≈ id-·ʳ

------------------------------------------------------------------------------
-- The trace of an endomorphism is a scalar: close `f : X ⇒ X` up with the unitors
-- into `unit ⊗₀ X ⇒ unit ⊗₀ X` and trace out `X`.  No wire enters or leaves the
-- loop, so what remains is an endomorphism of the unit — a scalar
--
--         ╭──── X ────╮
--         │           │
--      ┌──┴──┐        │
--      │  f  │        │
--      └──┬──┘        │
--         │           │
--         ╰──── X ────╯

trace-endo : X ⇒ X → Scalar
trace-endo f = trace (λ⇐ ∘ f ∘ λ⇒)

-- The (categorical) dimension of an object, also called the Euler characteristic,
-- is the trace of its identity. See https://ncatlab.org/nlab/show/trace.
-- If the category is a matrix category over a commutative ring, this coincides with
-- tr(Iₙ) = n, the usual dimension of a vector space/free module.

trace-dim : Obj → Scalar
trace-dim X = trace-endo (id {X})

-- The trace transports to the opposite monoidal category.

traced-Op : Traced monoidal-Op
traced-Op = record
  { symmetric    = symmetric-Op
  ; trace        = trace
  ; trace-resp-≈ = trace-resp-≈
  ; slide        = ⟺ slide
  ; tightenₗ     = tightenᵣ
  ; tightenᵣ     = tightenₗ
  ; vanishing₁   = vanishing₁
  ; vanishing₂   = trace⟨ trace⟨ assoc ⟩ ⟩ ○ vanishing₂
  ; superposing  = trace⟨ assoc ⟩ ○ superposing
  ; yanking      = trace⟨ braiding-selfInverse ⟩ ○ yanking
  }
