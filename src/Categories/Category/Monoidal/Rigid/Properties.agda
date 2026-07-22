{-# OPTIONS --without-K --safe #-}

-- Consequences of rigidity: rigidity transfers to the opposite monoidal category
-- (`rigidˡ-Op` / `rigidʳ-Op`), and duals are closed under tensor — `[ X ⊗ Y ]⁻¹`
-- with its cup/cap and the flip iso `[ X ⊗ Y ]⁻¹ ≅ Y ⁻¹ ⊗₀ X ⁻¹` (modules `Left`/`Right`).

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

module Categories.Category.Monoidal.Rigid.Properties
    {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

import Categories.Category.Monoidal.Rigid M as Rigid
open Rigid using (LeftRigid; RightRigid)
import Categories.Category.Monoidal.Rigid as RigidModule
import Categories.Category.Monoidal.Rigid.Dual as RigidDual

open import Categories.Category.Monoidal.Reasoning M
  using ( _⟩⊗⟨_; refl⟩⊗⟨_; _⟩⊗⟨refl; ⊗-cancel
        ; merge₁ˡ; merge₂ˡ; serialize₁₂; serialize₂₁
        ; split₁ʳ; split₁ˡ; split₁³; split₂ˡ; split₂³ )
open import Categories.Morphism.Reasoning C
  using ( assoc²αε; assoc²βε; assoc²δα; assoc²εβ; cancelʳ; cancelˡ
        ; elimʳ; elimˡ; extendʳ; pull-first; pullʳ; pullˡ
        ; pushˡ; reassoc-tail₅; switch-fromtoʳ )
open import Categories.Morphism C using (_≅_)
open import Categories.Category.Monoidal.Properties M
  using (coherence₁; coherence-inv₃; monoidal-Op)
open import Categories.Category.Monoidal.Reassociation M
  using ( α⇐-id⊗-commute; α⇒-⊗id-commute; λ⇐-assoc; λ⇒-assoc
        ; ρ⇐-assoc; pentagon-assoc; pentagon-collapse-inv; whisker-comm )
open import Categories.Category.Monoidal.CupCap M
  using ( cap-closeʳ; cap-closeʳ-natural; cap-slideʳ; cup-bendˡ
        ; cup-bendˡ-assoc; cup-nest; cup-openʳ; cup-openʳ-natural
        ; cup-slideˡ; unit-conjˡ )
import Categories.Category.Monoidal.Utilities M as MonUtil

open Category C
  using ( Obj; _⇒_; _≈_; id; _∘_; assoc; sym-assoc; identity²
        ; module HomReasoning )
open Monoidal M
open MonUtil.Shorthands
open HomReasoning

private
  variable
    A B W X Y Z : Obj

rigidʳ-Op : RightRigid → RigidModule.LeftRigid monoidal-Op
rigidʳ-Op R = record
  { _⁻¹ = Rigid.RightRigid._⁻¹ R
  ; η = Rigid.RightRigid.ε R
  ; ε = Rigid.RightRigid.η R
  ; snake₁ = assoc²αε ○ assoc ○ Rigid.RightRigid.snake₁ R
  ; snake₂ = assoc²αε ○ assoc ○ Rigid.RightRigid.snake₂ R
  }

rigidˡ-Op : LeftRigid → RigidModule.RightRigid monoidal-Op
rigidˡ-Op L = record
  { _⁻¹ = Rigid.LeftRigid._⁻¹ L
  ; η = Rigid.LeftRigid.ε L
  ; ε = Rigid.LeftRigid.η L
  ; snake₁ = assoc²αε ○ assoc ○ Rigid.LeftRigid.snake₁ L
  ; snake₂ = assoc²αε ○ assoc ○ Rigid.LeftRigid.snake₂ L
  }

module Left (L : LeftRigid) where
  open LeftRigid L using (_⁻¹; η; ε; snake₁; dual₁)
  open RigidDual M L
    using ( capˡ; capᵀ; capᵀ-cup; capᵀ-ε; cupᵀ; cupᵀ-unbend; cupˡ
          ; cupᵀ-η; cupᵀ-unique; dual-uniqueˡ; dual₁-cup; snakeˡ-wire
          ; snakeˡ-dual )

  infix 4 [_⊗_]⁻¹

  [_⊗_]⁻¹ : Obj → Obj → Obj
  [ X ⊗ Y ]⁻¹ = Y ⁻¹ ⊗₀ X ⁻¹

  private
    -- `ε`, with `k` run along its wire first.
    capₖ : {k : Y ⇒ X} → X ⁻¹ ⊗₀ Y ⇒ unit
    capₖ {k = k} = ε ∘ (id ⊗₁ k)

    unit-cap-natural :
      λ⇒ {X = unit ⊗₀ unit} ∘ (id {unit} ⊗₁ λ⇐ {X = unit})
      ≈ λ⇐ {X = unit} ∘ λ⇒ {X = unit}
    unit-cap-natural = unitorˡ-commute-from

    abstract
      unit-snakeˡ :
        ρ⇒ ∘ (id {unit} ⊗₁ λ⇒) ∘ α⇒ ∘ (λ⇐ ⊗₁ id) ∘ λ⇐ ≈ id
      unit-snakeˡ = begin
        ρ⇒ ∘ (id ⊗₁ λ⇒) ∘ α⇒ ∘ (λ⇐ ⊗₁ id) ∘ λ⇐
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (coherence-inv₃ ⟩⊗⟨refl) ⟩∘⟨ coherence-inv₃ ⟩
        ρ⇒ ∘ (id ⊗₁ λ⇒) ∘ α⇒ ∘ (ρ⇐ ⊗₁ id) ∘ ρ⇐  ≈⟨ refl⟩∘⟨ pullˡ triangle ⟩
        ρ⇒ ∘ (ρ⇒ ⊗₁ id) ∘ (ρ⇐ ⊗₁ id) ∘ ρ⇐
          ≈⟨ refl⟩∘⟨ cancelˡ (⊗-cancel unitorʳ.isoʳ identity²) ⟩
        ρ⇒ ∘ ρ⇐                                          ≈⟨ unitorʳ.isoʳ ⟩
        id                                               ∎

      unit-snakeʳ :
        λ⇒ ∘ (λ⇒ ⊗₁ id {unit}) ∘ α⇐ ∘ (id ⊗₁ λ⇐) ∘ ρ⇐ ≈ id
      unit-snakeʳ = begin
        λ⇒ ∘ (λ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ λ⇐) ∘ ρ⇐    ≈⟨ refl⟩∘⟨ pullˡ λ⇒-assoc ⟩
        λ⇒ ∘ λ⇒ ∘ (id ⊗₁ λ⇐) ∘ ρ⇐                 ≈⟨ refl⟩∘⟨ extendʳ unit-cap-natural ⟩
        λ⇒ ∘ λ⇐ ∘ λ⇒ ∘ ρ⇐                         ≈⟨ cancelˡ unitorˡ.isoʳ ⟩
        λ⇒ ∘ ρ⇐                                   ≈˘⟨ refl⟩∘⟨ coherence-inv₃ ⟩
        λ⇒ ∘ λ⇐                                   ≈⟨ unitorˡ.isoʳ ⟩
        id                                        ∎

  ⁻¹-unit-iso : unit ≅ unit ⁻¹
  ⁻¹-unit-iso = dual-uniqueˡ λ⇐ λ⇒ unit-snakeˡ unit-snakeʳ

  -- The tensor dual `[ X ⊗ Y ]⁻¹ = Y ⁻¹ ⊗₀ X ⁻¹` is dual to `X ⊗₀ Y` by nesting
  -- one bend inside the other — and that nesting is exactly why the dual reverses
  -- its factors: the `X`-bend has to reach around the `Y`-bend.
  --
  --                ⊗-cup                                ⊗-cap
  --
  --   X      Y     Y ⁻¹    X ⁻¹            ╭───────────────────────────╮
  --   │      │      │       │              │       ╭───────────╮       │
  --   │      ╰──────╯       │   ← η        │       │           │       │
  --   │         ↑ inner     │              │       │           │       │
  --   ╰─────────────────────╯   ← η      Y ⁻¹    X ⁻¹          X       Y
  --             ↑ outer                              ↑ inner ε
  --                                          ↑ outer ε

  ⊗-cup : unit ⇒ (X ⊗₀ Y) ⊗₀ [ X ⊗ Y ]⁻¹
  ⊗-cup = cup-nest η η

  ⊗-cap : [ X ⊗ Y ]⁻¹ ⊗₀ (X ⊗₀ Y) ⇒ unit
  ⊗-cap = ε ∘ (id ⊗₁ capˡ) ∘ α⇒

  private
    cupˡ-core : A ⊗₀ B ⇒ Y ⊗₀ ((Y ⁻¹ ⊗₀ A) ⊗₀ B)
    cupˡ-core = α⇒ ∘ (α⇒ ⊗₁ id) ∘ ((η ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)

    cupˡ-core-open : α⇒ ∘ (cupˡ {X = Y} {A} ⊗₁ id {B}) ≈ cupˡ-core
    cupˡ-core-open = refl⟩∘⟨ split₁³

    -- `cupˡ` is natural in `k`: walk `k` down the cup's three factors, past the
    -- associator, through the cup itself, and out along the unitor.
    cupˡ-natural : {k : A ⇒ B} →
      (id {X} ⊗₁ (id {X ⁻¹} ⊗₁ k)) ∘ cupˡ ≈ cupˡ ∘ k
    cupˡ-natural {k = k} = begin
      (id ⊗₁ (id ⊗₁ k)) ∘ cupˡ                  ≈˘⟨ extendʳ assoc-commute-from ⟩
      α⇒ ∘ ((id ⊗₁ id) ⊗₁ k) ∘ (η ⊗₁ id) ∘ λ⇐   ≈⟨ refl⟩∘⟨ pullˡ η-merge ⟩
      α⇒ ∘ (η ⊗₁ k) ∘ λ⇐                        ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩∘⟨refl ⟩
      α⇒ ∘ ((η ⊗₁ id) ∘ (id ⊗₁ k)) ∘ λ⇐         ≈⟨ refl⟩∘⟨ pullʳ (⟺ unitorˡ-commute-to) ⟩
      α⇒ ∘ (η ⊗₁ id) ∘ (λ⇐ ∘ k)                 ≈⟨ assoc²εβ ⟩
      cupˡ ∘ k                                  ∎
      where
        -- The `id ⊗₁ id` the associator left behind is absorbed by `η`'s whisker.
        η-merge : ((id ⊗₁ id) ⊗₁ k) ∘ (η ⊗₁ id) ≈ η ⊗₁ k
        η-merge = (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ○ ⟺ serialize₂₁

    cupˡ-dinatural : {f : X ⇒ Y} →
      (id {Y} ⊗₁ (dual₁ f ⊗₁ id {Z})) ∘ cupˡ ≈ (f ⊗₁ (id ⊗₁ id)) ∘ cupˡ
    cupˡ-dinatural {f = f} = begin
      (id ⊗₁ (dual₁ f ⊗₁ id)) ∘ cupˡ                   ≈˘⟨ extendʳ assoc-commute-from ⟩
      α⇒ ∘ ((id ⊗₁ dual₁ f) ⊗₁ id) ∘ (η ⊗₁ id) ∘ λ⇐    ≈⟨ refl⟩∘⟨ pullˡ merge₁ˡ ⟩
      α⇒ ∘ (((id ⊗₁ dual₁ f) ∘ η) ⊗₁ id) ∘ λ⇐          ≈⟨ refl⟩∘⟨ dual₁-cup ⟩⊗⟨refl ⟩∘⟨refl ⟩
      α⇒ ∘ (((f ⊗₁ id) ∘ η) ⊗₁ id) ∘ λ⇐                ≈˘⟨ refl⟩∘⟨ pullˡ merge₁ˡ ⟩
      α⇒ ∘ ((f ⊗₁ id) ⊗₁ id) ∘ (η ⊗₁ id) ∘ λ⇐          ≈⟨ extendʳ assoc-commute-from ⟩
      (f ⊗₁ (id ⊗₁ id)) ∘ cupˡ                         ∎

    cupˡ-map : {f : X ⇒ Y} {k : A ⇒ B} →
      (id {Y} ⊗₁ (dual₁ f ⊗₁ k)) ∘ cupˡ ≈ (f ⊗₁ id) ∘ cupˡ ∘ k
    cupˡ-map {f = f} {k} = begin
      (id ⊗₁ (dual₁ f ⊗₁ k)) ∘ cupˡ
        ≈⟨ (refl⟩⊗⟨ serialize₂₁) ⟩∘⟨refl ⟩
      (id ⊗₁ ((id ⊗₁ k) ∘ (dual₁ f ⊗₁ id))) ∘ cupˡ       ≈⟨ pushˡ split₂ˡ ⟩
      (id ⊗₁ (id ⊗₁ k)) ∘ (id ⊗₁ (dual₁ f ⊗₁ id)) ∘ cupˡ  ≈⟨ refl⟩∘⟨ cupˡ-dinatural ⟩
      (id ⊗₁ (id ⊗₁ k)) ∘ (f ⊗₁ (id ⊗₁ id)) ∘ cupˡ       ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
      (id ⊗₁ (id ⊗₁ k)) ∘ (f ⊗₁ id) ∘ cupˡ               ≈⟨ extendʳ (⟺ whisker-comm) ⟩
      (f ⊗₁ id) ∘ (id ⊗₁ (id ⊗₁ k)) ∘ cupˡ               ≈˘⟨ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
      (f ⊗₁ (id ⊗₁ id)) ∘ (id ⊗₁ (id ⊗₁ k)) ∘ cupˡ       ≈⟨ refl⟩∘⟨ cupˡ-natural ⟩
      (f ⊗₁ (id ⊗₁ id)) ∘ cupˡ ∘ k                       ≈⟨ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
      (f ⊗₁ id) ∘ cupˡ ∘ k                               ∎

    snakeˡ : {k : Z ⇒ Y} → (ρ⇒ ∘ (id ⊗₁ capₖ)) ∘ cupˡ ≈ k
    snakeˡ {k = k} = begin
      (ρ⇒ ∘ (id ⊗₁ capₖ)) ∘ cupˡ                   ≈⟨ (refl⟩∘⟨ split₂ˡ) ⟩∘⟨refl ⟩
      (ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ (id ⊗₁ k))) ∘ cupˡ  ≈⟨ assoc²βε ⟩
      ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ (id ⊗₁ k)) ∘ cupˡ    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cupˡ-natural ⟩
      ρ⇒ ∘ (id ⊗₁ ε) ∘ cupˡ ∘ k                    ≈⟨ assoc²εβ ⟩
      (ρ⇒ ∘ (id ⊗₁ ε) ∘ cupˡ) ∘ k                  ≈⟨ elimˡ snake₁ ⟩
      k                                            ∎

    cupˡ-core-fold :
      (id {Y} ⊗₁ α⇒ {Y ⁻¹} {A} {B}) ∘ cupˡ-core ≈ cupˡ
    cupˡ-core-fold = begin
      (id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘ ((η ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)
        ≈˘⟨ assoc²βε ⟩
      ((id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id)) ∘ ((η ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)
        ≈⟨ pentagon ⟩∘⟨refl ⟩
      (α⇒ ∘ α⇒) ∘ ((η ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)  ≈⟨ assoc ⟩
      α⇒ ∘ α⇒ ∘ ((η ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)    ≈⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
      α⇒ ∘ (η ⊗₁ (id ⊗₁ id)) ∘ α⇒ ∘ (λ⇐ ⊗₁ id)    ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
      α⇒ ∘ (η ⊗₁ id) ∘ α⇒ ∘ (λ⇐ ⊗₁ id)            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ λ⇐-assoc ⟩
      cupˡ                                        ∎

    cupˡ-assoc :
      (id {Y} ⊗₁ α⇒ {Y ⁻¹} {A} {B}) ∘ α⇒ ∘ (cupˡ {X = A} {Y = Y} ⊗₁ id {B})
      ≈ cupˡ
    cupˡ-assoc = cup-bendˡ-assoc η

    -- The same fold, under a whisker and between the associators the caller has it in.
    cupˡ-core-fold′ : (id {X ⊗₀ Y} ⊗₁ α⇒ {Y ⁻¹} {A} {B}) ∘ α⇐ ∘ (id ⊗₁ cupˡ-core)
                      ≈ α⇐ ∘ (id ⊗₁ cupˡ)
    cupˡ-core-fold′ = begin
      (id ⊗₁ α⇒) ∘ α⇐ ∘ (id ⊗₁ cupˡ-core)           ≈⟨ pullˡ α⇐-id⊗-commute ⟩
      (α⇐ ∘ (id ⊗₁ (id ⊗₁ α⇒))) ∘ (id ⊗₁ cupˡ-core) ≈⟨ pullʳ merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ ((id ⊗₁ α⇒) ∘ cupˡ-core))         ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ cupˡ-core-fold) ⟩
      α⇐ ∘ (id ⊗₁ cupˡ)                             ∎

    -- The cap `ε ∘ (id ⊗₁ k) ∘ α⇒`, whiskered by `X ⊗₀ Y` and fed the nested cup, is
    -- just `k` under the same whisker: `cupˡ-core-fold′` straightens the cup out and
    -- `snakeˡ` runs the loop.  (`⊗-cap` is this cap with `k = capˡ`.)
    inner-snake : {k : A ⊗₀ B ⇒ Y} →
      ρ⇒ ∘ (id {X ⊗₀ Y} ⊗₁ (ε ∘ (id ⊗₁ k) ∘ α⇒)) ∘ α⇐ ∘ (id ⊗₁ cupˡ-core)
      ≈ id ⊗₁ k
    inner-snake {k = k} = begin
      ρ⇒ ∘ (id ⊗₁ (ε ∘ (id ⊗₁ k) ∘ α⇒)) ∘ α⇐ ∘ (id ⊗₁ cupˡ-core)
        ≈⟨ refl⟩∘⟨ split₂³ ⟩∘⟨refl ⟩
      ρ⇒ ∘ ((id ⊗₁ ε) ∘ (id ⊗₁ (id ⊗₁ k)) ∘ (id ⊗₁ α⇒)) ∘ α⇐ ∘ (id ⊗₁ cupˡ-core)
        ≈⟨ refl⟩∘⟨ assoc²βε ⟩
      ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ (id ⊗₁ k)) ∘ (id ⊗₁ α⇒) ∘ α⇐ ∘ (id ⊗₁ cupˡ-core)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cupˡ-core-fold′ ⟩
      ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ (id ⊗₁ k)) ∘ α⇐ ∘ (id ⊗₁ cupˡ)
        ≈˘⟨ refl⟩∘⟨ assoc ⟩
      ρ⇒ ∘ ((id ⊗₁ ε) ∘ (id ⊗₁ (id ⊗₁ k))) ∘ α⇐ ∘ (id ⊗₁ cupˡ)
        ≈⟨ refl⟩∘⟨ merge₂ˡ ⟩∘⟨refl ⟩
      ρ⇒ ∘ (id ⊗₁ capₖ) ∘ α⇐ ∘ (id ⊗₁ cupˡ)        ≈⟨ sym-assoc ⟩
      cap-closeʳ capₖ ∘ α⇐ ∘ (id ⊗₁ cupˡ)          ≈⟨ pullˡ cap-closeʳ-natural ⟩
      (id ⊗₁ cap-closeʳ capₖ) ∘ (id ⊗₁ cupˡ)       ≈⟨ merge₂ˡ ⟩
      id ⊗₁ (cap-closeʳ capₖ ∘ cupˡ)               ≈⟨ refl⟩⊗⟨ snakeˡ ⟩
      id ⊗₁ k                                      ∎

    -- Bending `⊗-cup` into place plants the outer cup `cupˡ` and leaves the inner
    -- one, `cupˡ-core`, waiting under an associator for the cap to come and meet it.
    ⊗-cup-open : α⇒ ∘ (⊗-cup {X} {Y} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
      ≈ α⇐ ∘ (id ⊗₁ cupˡ-core) ∘ cupˡ
    ⊗-cup-open = begin
      α⇒ ∘ (⊗-cup ⊗₁ id) ∘ λ⇐                                         ≈⟨ refl⟩∘⟨ split₁³ ⟩∘⟨refl ⟩
      α⇒ ∘ ((α⇐ ⊗₁ id) ∘ ((id ⊗₁ cupˡ) ⊗₁ id) ∘ (η ⊗₁ id)) ∘ λ⇐       ≈⟨ cup-slideˡ ⟩
      ((α⇐ ∘ (id ⊗₁ (α⇒ ∘ (cupˡ ⊗₁ id)))) ∘ (α⇒ ∘ (η ⊗₁ id))) ∘ λ⇐
        ≈⟨ ((refl⟩∘⟨ refl⟩⊗⟨ cupˡ-core-open) ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((α⇐ ∘ (id ⊗₁ cupˡ-core)) ∘ (α⇒ ∘ (η ⊗₁ id))) ∘ λ⇐              ≈⟨ assoc²αε ⟩
      α⇐ ∘ (id ⊗₁ cupˡ-core) ∘ (α⇒ ∘ (η ⊗₁ id)) ∘ λ⇐                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
      α⇐ ∘ (id ⊗₁ cupˡ-core) ∘ cupˡ                                   ∎

    -- The `X ⊗₀ Y` snake: `⊗-cup-open` plants both cups, `inner-snake` runs the
    -- inner loop, and what is left is the outer one — the nested snake, straightened
    -- by `snakeˡ-wire`.
    ⊗-snakeˡ : ρ⇒ ∘ (id ⊗₁ ⊗-cap {X} {Y}) ∘ α⇒ ∘ (⊗-cup ⊗₁ id) ∘ λ⇐ ≈ id
    ⊗-snakeˡ = begin
      ρ⇒ ∘ (id ⊗₁ ⊗-cap) ∘ α⇒ ∘ (⊗-cup ⊗₁ id) ∘ λ⇐          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-cup-open ⟩
      ρ⇒ ∘ (id ⊗₁ ⊗-cap) ∘ α⇐ ∘ (id ⊗₁ cupˡ-core) ∘ cupˡ    ≈⟨ reassoc-tail₅ ⟩
      (ρ⇒ ∘ (id ⊗₁ ⊗-cap) ∘ α⇐ ∘ (id ⊗₁ cupˡ-core)) ∘ cupˡ  ≈⟨ inner-snake ⟩∘⟨refl ⟩
      (id ⊗₁ capˡ) ∘ cupˡ                                   ≈⟨ snakeˡ-wire ⟩
      id                                                    ∎

  abstract
    ⊗-cup-natural : {f : X ⇒ Y} {g : A ⇒ B} →
      (id ⊗₁ (dual₁ g ⊗₁ dual₁ f)) ∘ ⊗-cup
      ≈ ((f ⊗₁ g) ⊗₁ id) ∘ ⊗-cup
    ⊗-cup-natural {f = f} {g} = begin
      (id ⊗₁ (dual₁ g ⊗₁ dual₁ f)) ∘ α⇐ ∘ (id ⊗₁ cupˡ) ∘ η
        ≈⟨ extendʳ α⇐-id⊗-commute ⟩
      α⇐ ∘ (id ⊗₁ (id ⊗₁ (dual₁ g ⊗₁ dual₁ f))) ∘ (id ⊗₁ cupˡ) ∘ η
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ ((id ⊗₁ (dual₁ g ⊗₁ dual₁ f)) ∘ cupˡ)) ∘ η       ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ cupˡ-map) ⟩∘⟨refl ⟩
      α⇐ ∘ (id ⊗₁ ((g ⊗₁ id) ∘ cupˡ ∘ dual₁ f)) ∘ η
        ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ (g ⊗₁ id)) ∘ (id ⊗₁ (cupˡ ∘ dual₁ f)) ∘ η
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ (g ⊗₁ id)) ∘ (id ⊗₁ cupˡ) ∘ (id ⊗₁ dual₁ f) ∘ η
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ dual₁-cup ⟩
      α⇐ ∘ (id ⊗₁ (g ⊗₁ id)) ∘ (id ⊗₁ cupˡ) ∘ (f ⊗₁ id) ∘ η
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ whisker-comm ⟩
      α⇐ ∘ (id ⊗₁ (g ⊗₁ id)) ∘ (f ⊗₁ id) ∘ (id ⊗₁ cupˡ) ∘ η
        ≈⟨ refl⟩∘⟨ pullˡ (⟺ serialize₂₁) ⟩
      α⇐ ∘ (f ⊗₁ (g ⊗₁ id)) ∘ (id ⊗₁ cupˡ) ∘ η
        ≈⟨ extendʳ assoc-commute-to ⟩
      ((f ⊗₁ g) ⊗₁ id) ∘ ⊗-cup                            ∎

  -- `⊗-cup`/`⊗-cap` exhibit `[ X ⊗ Y ]⁻¹` as *a* dual of `X ⊗₀ Y`, and `η`/`ε`
  -- exhibit `(X ⊗₀ Y) ⁻¹` as *the* chosen one.  Duals are unique up to canonical
  -- iso, so the two are isomorphic — transpose one pair's cap along the other's.

  ⁻¹-flip-⊗ : [ X ⊗ Y ]⁻¹ ⇒ (X ⊗₀ Y) ⁻¹
  ⁻¹-flip-⊗ {X} {Y} = capᵀ ⊗-cap

  ⁻¹-flip-⊗⁻¹ : (X ⊗₀ Y) ⁻¹ ⇒ [ X ⊗ Y ]⁻¹
  ⁻¹-flip-⊗⁻¹ {X} {Y} = cupᵀ ⊗-cup

  private abstract
    cupˡ-cupᵀ : (cup : unit ⇒ X ⊗₀ Z) →
      (id {X} ⊗₁ (cupᵀ cup ⊗₁ id {A})) ∘ cupˡ
      ≈ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐
    cupˡ-cupᵀ cup = begin
      (id ⊗₁ (cupᵀ cup ⊗₁ id)) ∘ cupˡ
        ≈⟨ extendʳ (⟺ assoc-commute-from) ⟩
      α⇒ ∘ (((id ⊗₁ cupᵀ cup) ⊗₁ id) ∘ (η ⊗₁ id) ∘ λ⇐)
        ≈⟨ refl⟩∘⟨ pullˡ merge₁ˡ ⟩
      α⇒ ∘ ((((id ⊗₁ cupᵀ cup) ∘ η) ⊗₁ id) ∘ λ⇐)
        ≈⟨ refl⟩∘⟨ (cupᵀ-η cup ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐  ∎

  abstract
    cupˡ-⊗ :
      (id {X ⊗₀ Y} ⊗₁ (⁻¹-flip-⊗⁻¹ ⊗₁ id {Z})) ∘ cupˡ
      ≈ α⇒ ∘ (⊗-cup ⊗₁ id) ∘ λ⇐
    cupˡ-⊗ = cupˡ-cupᵀ ⊗-cup

    ⁻¹-flip-⊗⁻¹-natural : {f : X ⇒ Y} {g : A ⇒ B} →
      (dual₁ g ⊗₁ dual₁ f) ∘ ⁻¹-flip-⊗⁻¹
      ≈ ⁻¹-flip-⊗⁻¹ ∘ dual₁ (f ⊗₁ g)
    ⁻¹-flip-⊗⁻¹-natural {f = f} {g} = cupᵀ-unique (begin
      (id ⊗₁ ((dual₁ g ⊗₁ dual₁ f) ∘ ⁻¹-flip-⊗⁻¹)) ∘ η  ≈⟨ pushˡ split₂ˡ ⟩
      (id ⊗₁ (dual₁ g ⊗₁ dual₁ f)) ∘ (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ η
        ≈⟨ refl⟩∘⟨ cupᵀ-η ⊗-cup ⟩
      (id ⊗₁ (dual₁ g ⊗₁ dual₁ f)) ∘ ⊗-cup               ≈⟨ ⊗-cup-natural ⟩
      ((f ⊗₁ g) ⊗₁ id) ∘ ⊗-cup                           ≈˘⟨ refl⟩∘⟨ cupᵀ-η ⊗-cup ⟩
      ((f ⊗₁ g) ⊗₁ id) ∘ (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ η         ≈⟨ extendʳ whisker-comm ⟩
      (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ ((f ⊗₁ g) ⊗₁ id) ∘ η
        ≈˘⟨ refl⟩∘⟨ dual₁-cup ⟩
      (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ (id ⊗₁ dual₁ (f ⊗₁ g)) ∘ η   ≈⟨ pullˡ merge₂ˡ ⟩
      (id ⊗₁ (⁻¹-flip-⊗⁻¹ ∘ dual₁ (f ⊗₁ g))) ∘ η         ∎)

  private abstract
    ⊗-cup-dual : {f : X ⊗₀ Y ⇒ Z} {k : [ X ⊗ Y ]⁻¹ ⇒ A} →
      (id ⊗₁ (k ∘ ⁻¹-flip-⊗⁻¹ ∘ dual₁ f)) ∘ η
      ≈ (f ⊗₁ id) ∘ (id ⊗₁ k) ∘ ⊗-cup
    ⊗-cup-dual {f = f} {k} = begin
      (id ⊗₁ (k ∘ ⁻¹-flip-⊗⁻¹ ∘ dual₁ f)) ∘ η                ≈⟨ pushˡ split₂ˡ ⟩
      (id ⊗₁ k) ∘ (id ⊗₁ (⁻¹-flip-⊗⁻¹ ∘ dual₁ f)) ∘ η       ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      (id ⊗₁ k) ∘ (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ (id ⊗₁ dual₁ f) ∘ η ≈⟨ refl⟩∘⟨ refl⟩∘⟨ dual₁-cup ⟩
      (id ⊗₁ k) ∘ (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ (f ⊗₁ id) ∘ η        ≈⟨ refl⟩∘⟨ extendʳ (⟺ whisker-comm) ⟩
      (id ⊗₁ k) ∘ (f ⊗₁ id) ∘ (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ η        ≈⟨ extendʳ (⟺ whisker-comm) ⟩
      (f ⊗₁ id) ∘ (id ⊗₁ k) ∘ (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ η        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cupᵀ-η ⊗-cup ⟩
      (f ⊗₁ id) ∘ (id ⊗₁ k) ∘ ⊗-cup                          ∎

    ⊗-cup-nest₁ : (cup : unit ⇒ X ⊗₀ A) →
      (id {X ⊗₀ Y} ⊗₁ (id ⊗₁ cupᵀ cup)) ∘ ⊗-cup
      ≈ cup-nest cup η
    ⊗-cup-nest₁ cup = begin
      (id ⊗₁ (id ⊗₁ cupᵀ cup)) ∘ ⊗-cup
        ≈⟨ extendʳ α⇐-id⊗-commute ⟩
      α⇐ ∘ (id ⊗₁ (id ⊗₁ (id ⊗₁ cupᵀ cup))) ∘ (id ⊗₁ cupˡ) ∘ η
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ ((id ⊗₁ (id ⊗₁ cupᵀ cup)) ∘ cupˡ)) ∘ η
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ cupˡ-natural) ⟩∘⟨refl ⟩
      α⇐ ∘ (id ⊗₁ (cupˡ ∘ cupᵀ cup)) ∘ η          ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ cupˡ) ∘ (id ⊗₁ cupᵀ cup) ∘ η    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cupᵀ-η cup ⟩
      α⇐ ∘ (id ⊗₁ cupˡ) ∘ cup                     ∎

    ⊗-cup-nest₂ : (cup : unit ⇒ Y ⊗₀ A) →
      (id {X ⊗₀ Y} ⊗₁ (cupᵀ cup ⊗₁ id {X ⁻¹})) ∘ ⊗-cup
      ≈ cup-nest η cup
    ⊗-cup-nest₂ cup = begin
      (id ⊗₁ (cupᵀ cup ⊗₁ id)) ∘ ⊗-cup
        ≈⟨ extendʳ α⇐-id⊗-commute ⟩
      α⇐ ∘ (id ⊗₁ (id ⊗₁ (cupᵀ cup ⊗₁ id))) ∘ (id ⊗₁ cupˡ) ∘ η
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ ((id ⊗₁ (cupᵀ cup ⊗₁ id)) ∘ cupˡ)) ∘ η
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ cupˡ-cupᵀ cup ⟩∘⟨refl ⟩
      cup-nest η cup  ∎

    cup-bendˡ-nest-open :
      (cup₀ : unit ⇒ A ⊗₀ B) (cup₁ : unit ⇒ X ⊗₀ Y) →
      cup-bendˡ {A = Z} (cup-nest cup₀ cup₁)
      ≈ (α⇐ ∘ (id ⊗₁ (α⇒ ∘ (cup-bendˡ cup₁ ⊗₁ id)))) ∘ cup-bendˡ cup₀
    cup-bendˡ-nest-open cup₀ cup₁ = begin
      α⇒ ∘ (cup-nest cup₀ cup₁ ⊗₁ id) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ split₁³ ⟩∘⟨refl ⟩
      unit-conjˡ ((α⇐ ⊗₁ id) ∘ ((id ⊗₁ cup-bendˡ cup₁) ⊗₁ id) ∘ (cup₀ ⊗₁ id))
        ≈⟨ cup-slideˡ ⟩
      ((α⇐ ∘ (id ⊗₁ (α⇒ ∘ (cup-bendˡ cup₁ ⊗₁ id)))) ∘
        (α⇒ ∘ (cup₀ ⊗₁ id))) ∘ λ⇐
        ≈⟨ pullʳ assoc ⟩
      (α⇐ ∘ (id ⊗₁ (α⇒ ∘ (cup-bendˡ cup₁ ⊗₁ id)))) ∘ cup-bendˡ cup₀  ∎

    cup-bendˡ-nest :
      (cup₀ : unit ⇒ A ⊗₀ B) (cup₁ : unit ⇒ X ⊗₀ Y) →
      (id ⊗₁ α⇒) ∘ cup-bendˡ {A = Z} (cup-nest cup₀ cup₁)
      ≈ α⇐ ∘ (id ⊗₁ cup-bendˡ cup₁) ∘ cup-bendˡ cup₀
    cup-bendˡ-nest cup₀ cup₁ = begin
      (id ⊗₁ α⇒) ∘ cup-bendˡ (cup-nest cup₀ cup₁)
        ≈⟨ refl⟩∘⟨ cup-bendˡ-nest-open cup₀ cup₁ ⟩
      (id ⊗₁ α⇒) ∘
        ((α⇐ ∘ (id ⊗₁ (α⇒ ∘ (cup-bendˡ cup₁ ⊗₁ id)))) ∘ cup-bendˡ cup₀)
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (id ⊗₁ α⇒) ∘ α⇐ ∘
        (id ⊗₁ (α⇒ ∘ (cup-bendˡ cup₁ ⊗₁ id))) ∘ cup-bendˡ cup₀
        ≈⟨ extendʳ α⇐-id⊗-commute ⟩
      α⇐ ∘ (id ⊗₁ (id ⊗₁ α⇒)) ∘
        (id ⊗₁ (α⇒ ∘ (cup-bendˡ cup₁ ⊗₁ id))) ∘ cup-bendˡ cup₀
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ ((id ⊗₁ α⇒) ∘ α⇒ ∘ (cup-bendˡ cup₁ ⊗₁ id))) ∘ cup-bendˡ cup₀
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ cup-bendˡ-assoc cup₁) ⟩∘⟨refl ⟩
      α⇐ ∘ (id ⊗₁ cup-bendˡ cup₁) ∘ cup-bendˡ cup₀  ∎

    cup-nest-assoc :
      (cup₀ : unit ⇒ A ⊗₀ B) (cup₁ : unit ⇒ W ⊗₀ X) (cup₂ : unit ⇒ Y ⊗₀ Z) →
      (α⇒ ⊗₁ id) ∘ cup-nest (cup-nest cup₀ cup₁) cup₂
      ≈ (id ⊗₁ α⇒) ∘ cup-nest cup₀ (cup-nest cup₁ cup₂)
    cup-nest-assoc cup₀ cup₁ cup₂ = begin
      (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ cup-bendˡ cup₂) ∘ α⇐
        ∘ (id ⊗₁ cup-bendˡ cup₁) ∘ cup₀
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ α⇐-id⊗-commute ⟩
      (α⇒ ⊗₁ id) ∘ α⇐ ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ cup-bendˡ cup₂))
        ∘ (id ⊗₁ cup-bendˡ cup₁) ∘ cup₀
        ≈⟨ assoc²εβ ⟩
      ((α⇒ ⊗₁ id) ∘ α⇐ ∘ α⇐) ∘
        ((id ⊗₁ (id ⊗₁ cup-bendˡ cup₂)) ∘ (id ⊗₁ cup-bendˡ cup₁) ∘ cup₀)
        ≈⟨ pentagon-collapse-inv ⟩∘⟨refl ⟩
      (α⇐ ∘ (id ⊗₁ α⇐)) ∘
        ((id ⊗₁ (id ⊗₁ cup-bendˡ cup₂)) ∘ (id ⊗₁ cup-bendˡ cup₁) ∘ cup₀)
        ≈⟨ assoc ⟩
      α⇐ ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ cup-bendˡ cup₂))
        ∘ (id ⊗₁ cup-bendˡ cup₁) ∘ cup₀
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ ((id ⊗₁ cup-bendˡ cup₂) ∘ cup-bendˡ cup₁)) ∘ cup₀
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ (α⇐ ∘ (id ⊗₁ cup-bendˡ cup₂) ∘ cup-bendˡ cup₁)) ∘ cup₀
        ≈˘⟨ refl⟩∘⟨ (refl⟩⊗⟨ cup-bendˡ-nest cup₁ cup₂) ⟩∘⟨refl ⟩
      α⇐ ∘ (id ⊗₁ ((id ⊗₁ α⇒) ∘ cup-bendˡ (cup-nest cup₁ cup₂))) ∘ cup₀
        ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ (id ⊗₁ α⇒)) ∘ (id ⊗₁ cup-bendˡ (cup-nest cup₁ cup₂)) ∘ cup₀
        ≈⟨ extendʳ (⟺ α⇐-id⊗-commute) ⟩
      (id ⊗₁ α⇒) ∘ cup-nest cup₀ (cup-nest cup₁ cup₂)  ∎

  abstract
    ⊗-cup-assoc :
      (α⇒ {X} {Y} {Z} ⊗₁ id)
        ∘ (id ⊗₁ (id ⊗₁ ⁻¹-flip-⊗⁻¹)) ∘ ⊗-cup
      ≈ (id ⊗₁ α⇒) ∘ (id ⊗₁ (⁻¹-flip-⊗⁻¹ ⊗₁ id)) ∘ ⊗-cup
    ⊗-cup-assoc = begin
      (α⇒ ⊗₁ id) ∘ (id ⊗₁ (id ⊗₁ ⁻¹-flip-⊗⁻¹)) ∘ ⊗-cup  ≈⟨ refl⟩∘⟨ ⊗-cup-nest₁ ⊗-cup ⟩
      (α⇒ ⊗₁ id) ∘ cup-nest ⊗-cup η                       ≈⟨ cup-nest-assoc η η η ⟩
      (id ⊗₁ α⇒) ∘ cup-nest η ⊗-cup                       ≈˘⟨ refl⟩∘⟨ ⊗-cup-nest₂ ⊗-cup ⟩
      (id ⊗₁ α⇒) ∘ (id ⊗₁ (⁻¹-flip-⊗⁻¹ ⊗₁ id)) ∘ ⊗-cup  ∎

    ⁻¹-flip-⊗⁻¹-assoc :
      (id {Z ⁻¹} ⊗₁ ⁻¹-flip-⊗⁻¹ {X} {Y}) ∘ ⁻¹-flip-⊗⁻¹ ∘ dual₁ α⇒
      ≈ α⇒ ∘ (⁻¹-flip-⊗⁻¹ ⊗₁ id) ∘ ⁻¹-flip-⊗⁻¹
    ⁻¹-flip-⊗⁻¹-assoc = cupᵀ-unique (begin
      (id ⊗₁ ((id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ ⁻¹-flip-⊗⁻¹ ∘ dual₁ α⇒)) ∘ η
        ≈⟨ ⊗-cup-dual ⟩
      (α⇒ ⊗₁ id) ∘ (id ⊗₁ (id ⊗₁ ⁻¹-flip-⊗⁻¹)) ∘ ⊗-cup  ≈⟨ ⊗-cup-assoc ⟩
      (id ⊗₁ α⇒) ∘ (id ⊗₁ (⁻¹-flip-⊗⁻¹ ⊗₁ id)) ∘ ⊗-cup
        ≈˘⟨ refl⟩∘⟨ (refl⟩∘⟨ cupᵀ-η ⊗-cup) ⟩
      (id ⊗₁ α⇒) ∘ (id ⊗₁ (⁻¹-flip-⊗⁻¹ ⊗₁ id)) ∘ (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ η
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      (id ⊗₁ α⇒) ∘ (id ⊗₁ ((⁻¹-flip-⊗⁻¹ ⊗₁ id) ∘ ⁻¹-flip-⊗⁻¹)) ∘ η  ≈⟨ pullˡ merge₂ˡ ⟩
      (id ⊗₁ (α⇒ ∘ (⁻¹-flip-⊗⁻¹ ⊗₁ id) ∘ ⁻¹-flip-⊗⁻¹)) ∘ η  ∎)

    ⁻¹-flip-⊗⁻¹-unitaryˡ : (id {X ⁻¹} ⊗₁ _≅_.to ⁻¹-unit-iso) ∘ ⁻¹-flip-⊗⁻¹ ∘ dual₁ λ⇒ ≈ ρ⇐
    ⁻¹-flip-⊗⁻¹-unitaryˡ = cupᵀ-unique (begin
      (id ⊗₁ ((id ⊗₁ _≅_.to ⁻¹-unit-iso) ∘ ⁻¹-flip-⊗⁻¹ ∘ dual₁ λ⇒)) ∘ η
        ≈⟨ ⊗-cup-dual ⟩
      (λ⇒ ⊗₁ id) ∘ (id ⊗₁ (id ⊗₁ _≅_.to ⁻¹-unit-iso)) ∘ ⊗-cup
        ≈⟨ refl⟩∘⟨ ⊗-cup-nest₁ λ⇐ ⟩
      (λ⇒ ⊗₁ id) ∘ cup-nest λ⇐ η
        ≈⟨ pullˡ λ⇒-assoc ⟩
      λ⇒ ∘ (id ⊗₁ cupˡ) ∘ λ⇐                 ≈⟨ extendʳ unitorˡ-commute-from ⟩
      cupˡ ∘ λ⇒ ∘ λ⇐                         ≈⟨ elimʳ unitorˡ.isoʳ ⟩
      cupˡ                                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ ⟩
      α⇒ ∘ (η ⊗₁ id) ∘ ρ⇐                   ≈˘⟨ refl⟩∘⟨ unitorʳ-commute-to ⟩
      α⇒ ∘ ρ⇐ ∘ η                            ≈⟨ pullˡ (⟺ ρ⇐-assoc) ⟩
      (id ⊗₁ ρ⇐) ∘ η                        ∎)

    ⁻¹-flip-⊗⁻¹-unitaryʳ : (_≅_.to ⁻¹-unit-iso ⊗₁ id {X ⁻¹}) ∘ ⁻¹-flip-⊗⁻¹ ∘ dual₁ ρ⇒ ≈ λ⇐
    ⁻¹-flip-⊗⁻¹-unitaryʳ = cupᵀ-unique (begin
      (id ⊗₁ ((_≅_.to ⁻¹-unit-iso ⊗₁ id) ∘ ⁻¹-flip-⊗⁻¹ ∘ dual₁ ρ⇒)) ∘ η
        ≈⟨ ⊗-cup-dual ⟩
      (ρ⇒ ⊗₁ id) ∘ (id ⊗₁ (_≅_.to ⁻¹-unit-iso ⊗₁ id)) ∘ ⊗-cup
        ≈⟨ refl⟩∘⟨ ⊗-cup-nest₂ λ⇐ ⟩
      (ρ⇒ ⊗₁ id) ∘ cup-nest η λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ pullˡ λ⇐-assoc) ⟩∘⟨refl ⟩
      (ρ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ (λ⇐ ∘ λ⇐)) ∘ η
        ≈⟨ pullˡ (⟺ (switch-fromtoʳ associator triangle)) ⟩
      (id ⊗₁ λ⇒) ∘ (id ⊗₁ (λ⇐ ∘ λ⇐)) ∘ η       ≈⟨ pullˡ merge₂ˡ ⟩
      (id ⊗₁ (λ⇒ ∘ (λ⇐ ∘ λ⇐))) ∘ η             ≈⟨ (refl⟩⊗⟨ cancelˡ unitorˡ.isoʳ) ⟩∘⟨refl ⟩
      (id ⊗₁ λ⇐) ∘ η                            ∎)

    ⁻¹-flip-⊗-cup : (id {X ⊗₀ Y} ⊗₁ ⁻¹-flip-⊗) ∘ ⊗-cup ≈ η
    ⁻¹-flip-⊗-cup = capᵀ-cup ⊗-snakeˡ

    ⁻¹-flip-⊗-cap : ε {X ⊗₀ Y} ∘ (⁻¹-flip-⊗ ⊗₁ id) ≈ ⊗-cap
    ⁻¹-flip-⊗-cap = capᵀ-ε ⊗-cap

  private abstract
    snakeʳ : [ X ⊗ Y ]⁻¹ ⇒ [ X ⊗ Y ]⁻¹
    snakeʳ = λ⇒ ∘ (⊗-cap ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ ⊗-cup) ∘ ρ⇐

    snakeʳ-cap : ([ X ⊗ Y ]⁻¹ ⊗₀ (X ⊗₀ Y)) ⊗₀ [ X ⊗ Y ]⁻¹ ⇒ unit ⊗₀ [ X ⊗ Y ]⁻¹
    snakeʳ-cap = (ε ⊗₁ id) ∘ ((id ⊗₁ capˡ) ⊗₁ id) ∘ (α⇒ ⊗₁ id)

    nested-cup : unit ⇒ X ⊗₀ (Y ⊗₀ [ X ⊗ Y ]⁻¹)
    nested-cup {X} = (id ⊗₁ cupˡ {X = X ⁻¹}) ∘ η

    -- `id ⊗₁ ⊗-cup` with only its leading associator split off — the shape
    -- `⊗-snakeʳ` produces (via `split₂ˡ`) and `snakeʳ-core-fold` consumes.
    snakeʳ-cup : [ X ⊗ Y ]⁻¹ ⊗₀ unit ⇒ [ X ⊗ Y ]⁻¹ ⊗₀ ((X ⊗₀ Y) ⊗₀ [ X ⊗ Y ]⁻¹)
    snakeʳ-cup = (id ⊗₁ α⇐) ∘ (id ⊗₁ nested-cup)

    nested-cap : ([ X ⊗ Y ]⁻¹ ⊗₀ (X ⊗₀ Y)) ⊗₀ [ X ⊗ Y ]⁻¹ ⇒ (Y ⁻¹ ⊗₀ Y) ⊗₀ [ X ⊗ Y ]⁻¹
    nested-cap = ((id ⊗₁ capˡ) ∘ α⇒) ⊗₁ id

    capˡ-absorbs-α-core :
      α⇒ {unit} {Y} {W} ∘ (((ε {X} ⊗₁ id) ∘ α⇐) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)
      ≈ (ε ⊗₁ id) ∘ α⇐
    capˡ-absorbs-α-core = begin
      α⇒ ∘ (((ε ⊗₁ id) ∘ α⇐) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)           ≈⟨ refl⟩∘⟨ split₁ˡ ⟩∘⟨refl ⟩
      α⇒ ∘ (((ε ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ α⇐)   ≈⟨ refl⟩∘⟨ assoc ⟩
      α⇒ ∘ ((ε ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)     ≈⟨ pullˡ α⇒-⊗id-commute ⟩
      ((ε ⊗₁ id) ∘ α⇒) ∘ (α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)           ≈⟨ assoc ⟩
      (ε ⊗₁ id) ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)             ≈⟨ refl⟩∘⟨ assoc²εβ ⟩
      (ε ⊗₁ id) ∘ (α⇒ ∘ (α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)
        ≈⟨ refl⟩∘⟨ pentagon-assoc ⟩∘⟨refl ⟩
      (ε ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ α⇒)) ∘ (id ⊗₁ α⇐)
        ≈⟨ refl⟩∘⟨ cancelʳ (⊗-cancel identity² associator.isoʳ) ⟩
      (ε ⊗₁ id) ∘ α⇐                                            ∎

    capˡ-absorbs-α : (capˡ {X} {Y} ⊗₁ id {W}) ∘ α⇐ ∘ (id ⊗₁ α⇐) ≈ capˡ
    capˡ-absorbs-α = begin
      (capˡ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)                              ≈⟨ split₁ʳ ⟩∘⟨refl ⟩
      ((λ⇒ ⊗₁ id) ∘ (((ε ⊗₁ id) ∘ α⇐) ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ α⇐)   ≈⟨ assoc ⟩
      (λ⇒ ⊗₁ id) ∘ ((((ε ⊗₁ id) ∘ α⇐) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))   ≈˘⟨ coherence₁ ⟩∘⟨refl ⟩
      (λ⇒ ∘ α⇒) ∘ (((ε ⊗₁ id) ∘ α⇐) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)      ≈⟨ assoc ⟩
      λ⇒ ∘ (α⇒ ∘ (((ε ⊗₁ id) ∘ α⇐) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))      ≈⟨ refl⟩∘⟨ capˡ-absorbs-α-core ⟩
      capˡ                                                        ∎

    snakeʳ-core : [ X ⊗ Y ]⁻¹ ⇒ (Y ⁻¹ ⊗₀ Y) ⊗₀ [ X ⊗ Y ]⁻¹
    snakeʳ-core = nested-cap ∘ α⇐ ∘ snakeʳ-cup ∘ ρ⇐

    nested-cap-slide : nested-cap {X} {Y} ∘ α⇐ ∘ (id {[ X ⊗ Y ]⁻¹} ⊗₁ α⇐)
      ≈ α⇐ ∘ (id ⊗₁ capˡ) ∘ α⇒
    nested-cap-slide = begin
      nested-cap ∘ α⇐ ∘ (id ⊗₁ α⇐)  ≈⟨ cap-slideʳ ⟩
      α⇐ ∘ (id ⊗₁ ((capˡ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))) ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ capˡ-absorbs-α ⟩∘⟨refl ⟩
      α⇐ ∘ (id ⊗₁ capˡ) ∘ α⇒        ∎

    snakeʳ-core-fold : snakeʳ-core {X} {Y} ≈ α⇐ ∘ (id ⊗₁ cupˡ)
    snakeʳ-core-fold = begin
      snakeʳ-core                                                  ≈⟨ refl⟩∘⟨ assoc²δα ⟩
      nested-cap ∘ (((α⇐ ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ nested-cup)) ∘ ρ⇐)
        ≈⟨ pull-first nested-cap-slide ⟩
      (α⇐ ∘ (id ⊗₁ capˡ) ∘ α⇒) ∘ ((id ⊗₁ nested-cup) ∘ ρ⇐)          ≈⟨ assoc²βε ⟩
      α⇐ ∘ (id ⊗₁ capˡ) ∘ (α⇒ ∘ cup-openʳ nested-cup)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cup-openʳ-natural ⟩
      α⇐ ∘ (id ⊗₁ capˡ) ∘ (id ⊗₁ cup-openʳ nested-cup)              ≈⟨ refl⟩∘⟨ merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ (capˡ ∘ (id ⊗₁ nested-cup) ∘ ρ⇐))
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ cupᵀ-unbend ⟩
      α⇐ ∘ (id ⊗₁ cupˡ)                                             ∎

    ⊗-snakeʳ : λ⇒ ∘ (⊗-cap {X} {Y} ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ ⊗-cup) ∘ ρ⇐ ≈ id
    ⊗-snakeʳ = begin
      snakeʳ
        ≈⟨ refl⟩∘⟨ split₁³ ⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
      λ⇒ ∘ snakeʳ-cap ∘ α⇐ ∘ snakeʳ-cup ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ merge₁ˡ) ⟩∘⟨refl ⟩
      λ⇒ ∘ ((ε ⊗₁ id) ∘ nested-cap) ∘ α⇐ ∘ snakeʳ-cup ∘ ρ⇐  ≈⟨ refl⟩∘⟨ assoc ⟩
      λ⇒ ∘ (ε ⊗₁ id) ∘ snakeʳ-core                          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ snakeʳ-core-fold ⟩
      λ⇒ ∘ (ε ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ cupˡ)                    ≈˘⟨ assoc²βε ⟩
      capˡ ∘ (id ⊗₁ cupˡ)                                   ≈⟨ snakeˡ-dual ⟩
      id                                                    ∎

  -- `Y ⁻¹ ⊗₀ X ⁻¹` and the chosen dual `(X ⊗₀ Y) ⁻¹` are both left duals of
  -- `X ⊗₀ Y` — the former via `⊗-cup`/`⊗-cap` (with snakes `⊗-snakeˡ`/`⊗-snakeʳ`),
  -- the latter canonically — so the flip isomorphism is just an instance of the
  -- uniqueness of left duals.  Its `from`/`to` are `⁻¹-flip-⊗`/`⁻¹-flip-⊗⁻¹`.
  ⁻¹-flip-⊗-iso : [ X ⊗ Y ]⁻¹ ≅ (X ⊗₀ Y) ⁻¹
  ⁻¹-flip-⊗-iso = dual-uniqueˡ ⊗-cup ⊗-cap ⊗-snakeˡ ⊗-snakeʳ

module Right (R : RightRigid) where
  open RigidDual monoidal-Op (rigidʳ-Op R) public
