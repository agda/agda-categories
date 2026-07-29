{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

-- Cup and cap calculus in a monoidal category.
-- A cup is a morphism `unit ⇒ X`, drawn as creating `X` from no input wires.
-- A cap is a morphism `X ⇒ unit`, drawn as consuming `X`.

-- In the delooping view (https://ncatlab.org/nlab/show/delooping+hypothesis),
-- which views a monoidal category as a bicategory on one object, caps and cups are
-- 2-cells that create or consume the 1-cell `X` from the "identity" 1-cell `unit`.

module Categories.Category.Monoidal.CupCap
  {o ℓ e} {𝒞 : Category o ℓ e} (M : Monoidal 𝒞) where

open Category 𝒞
  using (Obj; _⇒_; _≈_; id; _∘_; assoc; sym-assoc; identity²)
open Monoidal M

open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Morphism.Reasoning 𝒞

open Shorthands

private
  variable
    A B C X Y Z : Obj

-- Opening a cup beside a spectator wire, and closing a cap beside one.  A cup
-- `unit ⇒ X` is introduced against the spectator `A` by an inverse unitor, and a
-- cap `X ⇒ unit` is absorbed into it by a unitor; the ˡ/ʳ says which side of `A`
-- the cup or cap sits on.  Every cup and cap in sight is built from these.
-- Diagrams read bottom-to-top.
--
--       cup-openˡ cup          cup-openʳ cup
--
--       X       A              A       X
--     ┌─┴─┐     │              │     ┌─┴─┐
--     │cup│     │              │     │cup│
--     └───┘     │              │     └───┘
--               A              A
--
--       cap-closeˡ cap         cap-closeʳ cap
--
--              A                     A
--              │                     │
--       X      A               A     X
--     ┌─┴─┐    │               │   ┌─┴─┐
--     │cap│    │               │   │cap│
--     └───┘    │               │   └───┘

module Operations where
  cup-openˡ : unit ⇒ X → A ⇒ X ⊗₀ A
  cup-openˡ cup = (cup ⊗₁ id) ∘ λ⇐

  cup-openʳ : unit ⇒ X → A ⇒ A ⊗₀ X
  cup-openʳ cup = (id ⊗₁ cup) ∘ ρ⇐

  cap-closeˡ : X ⇒ unit → X ⊗₀ A ⇒ A
  cap-closeˡ cap = λ⇒ ∘ (cap ⊗₁ id)

  cap-closeʳ : X ⇒ unit → A ⊗₀ X ⇒ A
  cap-closeʳ cap = ρ⇒ ∘ (id ⊗₁ cap)

  cup-bendˡ : unit ⇒ X ⊗₀ Y → A ⇒ X ⊗₀ (Y ⊗₀ A)
  cup-bendˡ cup = α⇒ ∘ cup-openˡ cup

  cup-bendʳ : unit ⇒ X ⊗₀ Y → A ⇒ (A ⊗₀ X) ⊗₀ Y
  cup-bendʳ cup = α⇐ ∘ cup-openʳ cup

  -- A cap on a *pair* has to reassociate first to reach its two wires.  Bending
  -- `cap : X ⊗₀ Y ⇒ unit` around a spectator `A` on the right is `cap-bendˡ`;
  -- the corresponding right-handed bend is `cap-bendʳ`, and `cap-reassoc`
  -- below says the two agree.

  cap-bendˡ : X ⊗₀ Y ⇒ unit → X ⊗₀ (Y ⊗₀ A) ⇒ A
  cap-bendˡ cap = cap-closeˡ cap ∘ α⇐

  cap-bendʳ : X ⊗₀ Y ⇒ unit → (A ⊗₀ X) ⊗₀ Y ⇒ A
  cap-bendʳ cap = cap-closeʳ cap ∘ α⇒

  cup-nest :
    unit ⇒ A ⊗₀ B → unit ⇒ X ⊗₀ Y →
    unit ⇒ (A ⊗₀ X) ⊗₀ (Y ⊗₀ B)
  cup-nest cup cup′ = α⇐ ∘ (id ⊗₁ cup-bendˡ cup′) ∘ cup

  -- `cup′` is planted inside `cup`; hence the output order `A`, `X`, `Y`, `B`.
  --
  --       A       X       Y       B
  --       │     ┌─┴───────┴─┐     │
  --       │     │   cup′    │     │
  --       │     └───────────┘     │
  --     ┌─┴───────────────────────┴──┐
  --     │            cup             │
  --     └────────────────────────────┘

  -- Conjugate a morphism by a unitor and the associator.  `unit-conjˡ f` feeds
  -- `f` a unit on the left (via `λ⇐`) and reassociates its output to the right;
  -- `unit-conjʳ` mirrors it on the right (via `ρ⇐`).  A cup bent into place is
  -- exactly one of these applied to a whiskered cup: `unit-conjˡ (cup ⊗₁ id)` is
  -- `α⇒ ∘ cup-openˡ cup`, and `unit-conjʳ (id ⊗₁ cup)` is `α⇐ ∘ cup-openʳ cup`.

  unit-conjˡ : (unit ⊗₀ X ⇒ (A ⊗₀ B) ⊗₀ Y) → (X ⇒ A ⊗₀ (B ⊗₀ Y))
  unit-conjˡ f = α⇒ ∘ f ∘ λ⇐

  unit-conjʳ : (X ⊗₀ unit ⇒ A ⊗₀ (B ⊗₀ Y)) → (X ⇒ (A ⊗₀ B) ⊗₀ Y)
  unit-conjʳ f = α⇐ ∘ f ∘ ρ⇐

open Operations public

module Congruence where
  cup-openˡ-resp : {cup cup′ : unit ⇒ Z} →
    cup ≈ cup′ → cup-openˡ {A = A} cup ≈ cup-openˡ cup′
  cup-openˡ-resp cup≈cup′ = ((cup≈cup′ ⟩⊗⟨refl) ⟩∘⟨refl)

  cup-openʳ-resp : {cup cup′ : unit ⇒ Z} →
    cup ≈ cup′ → cup-openʳ {A = A} cup ≈ cup-openʳ cup′
  cup-openʳ-resp cup≈cup′ = ((refl⟩⊗⟨ cup≈cup′) ⟩∘⟨refl)

  cap-closeˡ-resp : {cap cap′ : Z ⇒ unit} →
    cap ≈ cap′ → cap-closeˡ {A = A} cap ≈ cap-closeˡ cap′
  cap-closeˡ-resp cap≈cap′ = refl⟩∘⟨ (cap≈cap′ ⟩⊗⟨refl)

  cap-closeʳ-resp : {cap cap′ : Z ⇒ unit} →
    cap ≈ cap′ → cap-closeʳ {A = A} cap ≈ cap-closeʳ cap′
  cap-closeʳ-resp cap≈cap′ = refl⟩∘⟨ (refl⟩⊗⟨ cap≈cap′)

  cup-bendˡ-resp : {cup cup′ : unit ⇒ X ⊗₀ Y} →
    cup ≈ cup′ → cup-bendˡ {A = A} cup ≈ cup-bendˡ cup′
  cup-bendˡ-resp cup≈cup′ = refl⟩∘⟨ cup-openˡ-resp cup≈cup′

  cup-bendʳ-resp : {cup cup′ : unit ⇒ X ⊗₀ Y} →
    cup ≈ cup′ → cup-bendʳ {A = A} cup ≈ cup-bendʳ cup′
  cup-bendʳ-resp cup≈cup′ = refl⟩∘⟨ cup-openʳ-resp cup≈cup′

  cap-bendˡ-resp : {cap cap′ : X ⊗₀ Y ⇒ unit} →
    cap ≈ cap′ → cap-bendˡ {A = A} cap ≈ cap-bendˡ cap′
  cap-bendˡ-resp cap≈cap′ = cap-closeˡ-resp cap≈cap′ ⟩∘⟨refl

  cap-bendʳ-resp : {cap cap′ : X ⊗₀ Y ⇒ unit} →
    cap ≈ cap′ → cap-bendʳ {A = A} cap ≈ cap-bendʳ cap′
  cap-bendʳ-resp cap≈cap′ = cap-closeʳ-resp cap≈cap′ ⟩∘⟨refl

open Congruence public

-- A morphism on the spectator wire commutes through a cup or cap.
module Cup (cup : unit ⇒ Z) where
  cup-openˡ-∘ : {f : Z ⇒ Y} →
    (f ⊗₁ id {A}) ∘ cup-openˡ cup ≈ cup-openˡ (f ∘ cup)
  cup-openˡ-∘ = pullˡ merge₁ˡ

  cup-openʳ-∘ : {f : Z ⇒ Y} →
    (id {A} ⊗₁ f) ∘ cup-openʳ cup ≈ cup-openʳ (f ∘ cup)
  cup-openʳ-∘ = pullˡ merge₂ˡ

  cup-openˡ-commute : {f : A ⇒ B} →
    (id ⊗₁ f) ∘ cup-openˡ cup ≈ cup-openˡ {A = B} cup ∘ f
  cup-openˡ-commute = pullˡ (⟺ whisker-comm) ○ extendˡ (⟺ unitorˡ-commute-to)

  cup-openʳ-commute : {f : A ⇒ B} →
    (f ⊗₁ id) ∘ cup-openʳ cup ≈ cup-openʳ {A = B} cup ∘ f
  cup-openʳ-commute = pullˡ whisker-comm ○ extendˡ (⟺ unitorʳ-commute-to)

open Cup public

module Cap (cap : Z ⇒ unit) where
  cap-closeˡ-∘ : {f : Y ⇒ Z} →
    cap-closeˡ cap ∘ (f ⊗₁ id {A}) ≈ cap-closeˡ (cap ∘ f)
  cap-closeˡ-∘ = pullʳ merge₁ˡ

  cap-closeʳ-∘ : {f : Y ⇒ Z} →
    cap-closeʳ cap ∘ (id {A} ⊗₁ f) ≈ cap-closeʳ (cap ∘ f)
  cap-closeʳ-∘ = pullʳ merge₂ˡ

  cap-closeˡ-commute : {f : A ⇒ B} →
    cap-closeˡ cap ∘ (id ⊗₁ f) ≈ f ∘ cap-closeˡ {A = A} cap
  cap-closeˡ-commute = pullʳ whisker-comm ○ extendʳ unitorˡ-commute-from

  cap-closeʳ-commute : {f : A ⇒ B} →
    cap-closeʳ cap ∘ (f ⊗₁ id) ≈ f ∘ cap-closeʳ cap
  cap-closeʳ-commute = pullʳ (⟺ whisker-comm) ○ extendʳ unitorʳ-commute-from

open Cap public

module BentCup (cup : unit ⇒ X ⊗₀ Y) where
  cup-bendˡ-commute : {f : A ⇒ B} →
    (id ⊗₁ (id ⊗₁ f)) ∘ cup-bendˡ cup ≈ cup-bendˡ {A = B} cup ∘ f
  cup-bendˡ-commute = pullˡ (⟺ α⇒-id⊗-commute) ○ extendˡ (cup-openˡ-commute cup)

  cup-bendʳ-commute : {f : A ⇒ B} →
    ((f ⊗₁ id {X}) ⊗₁ id {Y}) ∘ cup-bendʳ cup ≈ cup-bendʳ {A = B} cup ∘ f
  cup-bendʳ-commute = pullˡ (⟺ α⇐-⊗id-commute) ○ extendˡ (cup-openʳ-commute cup)

  cup-bendˡ-⊗ : {f : X ⇒ Z} {g : Y ⇒ B} →
    (f ⊗₁ (g ⊗₁ id {A})) ∘ cup-bendˡ cup ≈ cup-bendˡ ((f ⊗₁ g) ∘ cup)
  cup-bendˡ-⊗ = pullˡ (⟺ assoc-commute-from) ○ pullʳ (cup-openˡ-∘ cup)

  cup-bendʳ-⊗ : {f : X ⇒ Z} {g : Y ⇒ B} →
    ((id {A} ⊗₁ f) ⊗₁ g) ∘ cup-bendʳ cup ≈ cup-bendʳ ((f ⊗₁ g) ∘ cup)
  cup-bendʳ-⊗ = pullˡ (⟺ assoc-commute-to) ○ pullʳ (cup-openʳ-∘ cup)

open BentCup public

module BentCap (cap : X ⊗₀ Y ⇒ unit) where
  cap-bendˡ-commute : {f : A ⇒ B} →
    cap-bendˡ cap ∘ (id ⊗₁ (id ⊗₁ f)) ≈ f ∘ cap-bendˡ {A = A} cap
  cap-bendˡ-commute = pullʳ (⟺ α⇐-id⊗-commute) ○ extendʳ (cap-closeˡ-commute cap)

  cap-bendʳ-commute : {f : A ⇒ B} →
    cap-bendʳ cap ∘ ((f ⊗₁ id {X}) ⊗₁ id {Y}) ≈ f ∘ cap-bendʳ cap
  cap-bendʳ-commute = pullʳ α⇒-⊗id-commute ○ extendʳ (cap-closeʳ-commute cap)

  cap-bendˡ-⊗ : {f : Z ⇒ X} {g : B ⇒ Y} →
    cap-bendˡ cap ∘ (f ⊗₁ (g ⊗₁ id {A})) ≈ cap-bendˡ (cap ∘ (f ⊗₁ g))
  cap-bendˡ-⊗ = pullʳ assoc-commute-to ○ pullˡ (cap-closeˡ-∘ cap)

  cap-bendʳ-⊗ : {f : Z ⇒ X} {g : B ⇒ Y} →
    cap-bendʳ cap ∘ ((id {A} ⊗₁ f) ⊗₁ g) ≈ cap-bendʳ (cap ∘ (f ⊗₁ g))
  cap-bendʳ-⊗ = pullʳ assoc-commute-from ○ pullˡ (cap-closeʳ-∘ cap)

open BentCap public

module Coherence where
  -- Opening a cup beside `A ⊗₀ B` can be done beside one factor at a time.
  cup-openˡ-natural : {cup : unit ⇒ Z} →
    α⇒ ∘ (cup-openˡ {A = A} cup ⊗₁ id {B}) ≈ cup-openˡ cup
  cup-openˡ-natural {cup = cup} = begin
    α⇒ ∘ (((cup ⊗₁ id) ∘ λ⇐) ⊗₁ id)        ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    α⇒ ∘ ((cup ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)  ≈⟨ extendʳ α⇒-⊗id-commute ⟩
    (cup ⊗₁ id) ∘ α⇒ ∘ (λ⇐ ⊗₁ id)          ≈⟨ refl⟩∘⟨ λ⇐-assoc ⟩
    cup-openˡ cup                           ∎

  cup-openʳ-natural : {cup : unit ⇒ Z} →
    α⇒ {A} {B} {Z} ∘ cup-openʳ cup ≈ id ⊗₁ cup-openʳ cup
  cup-openʳ-natural {cup = cup} = begin
    α⇒ ∘ (id ⊗₁ cup) ∘ ρ⇐             ≈⟨ extendʳ α⇒-id⊗-commute ⟩
    (id ⊗₁ (id ⊗₁ cup)) ∘ α⇒ ∘ ρ⇐     ≈˘⟨ refl⟩∘⟨ ρ⇐-assoc ⟩
    (id ⊗₁ (id ⊗₁ cup)) ∘ (id ⊗₁ ρ⇐)  ≈⟨ merge₂ˡ ⟩
    id ⊗₁ cup-openʳ cup               ∎

  cap-closeˡ-natural : {cap : Z ⇒ unit} →
    cap-closeˡ cap ∘ α⇒ {Z} {A} {B} ≈ cap-closeˡ cap ⊗₁ id
  cap-closeˡ-natural {cap = cap} = begin
    cap-closeˡ cap ∘ α⇒                       ≈⟨ assoc ⟩
    λ⇒ ∘ (cap ⊗₁ id) ∘ α⇒                     ≈˘⟨ refl⟩∘⟨ α⇒-⊗id-commute ⟩
    λ⇒ ∘ α⇒ ∘ ((cap ⊗₁ id) ⊗₁ id)             ≈⟨ pullˡ coherence₁ ⟩
    (λ⇒ ⊗₁ id) ∘ ((cap ⊗₁ id) ⊗₁ id)          ≈⟨ merge₁ˡ ⟩
    cap-closeˡ cap ⊗₁ id                      ∎

  cap-closeʳ-natural : {cap : Z ⇒ unit} →
    cap-closeʳ {A = A ⊗₀ B} cap ∘ α⇐ {A} {B} {Z} ≈ id ⊗₁ cap-closeʳ cap
  cap-closeʳ-natural {cap = cap} = begin
    cap-closeʳ cap ∘ α⇐               ≈⟨ pullʳ α⇐-id⊗-commute ⟩
    ρ⇒ ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ cap))     ≈⟨ pullˡ ρ⇒-assoc ⟩
    (id ⊗₁ ρ⇒) ∘ (id ⊗₁ (id ⊗₁ cap))  ≈⟨ merge₂ˡ ⟩
    id ⊗₁ cap-closeʳ cap              ∎

  -- The same fact, with the associator moved to the other side.
  cap-closeʳ-assoc : {cap : Z ⇒ unit} →
    cap-closeʳ {A = A ⊗₀ B} cap ≈ (id ⊗₁ cap-closeʳ cap) ∘ α⇒ {A} {B} {Z}
  cap-closeʳ-assoc = switch-tofromʳ associator cap-closeʳ-natural

  -- Whiskering a right-opened cup by `B` and reassociating drops it onto the `B`
  -- wire, where it is a left-opened cup.  `A` is a spectator on both sides.
  cup-openʳ-whisker : {cup : unit ⇒ Z} →
    α⇒ ∘ (cup-openʳ {A = A} cup ⊗₁ id {B}) ≈ id ⊗₁ cup-openˡ cup
  cup-openʳ-whisker {cup = cup} = begin
    α⇒ ∘ (((id ⊗₁ cup) ∘ ρ⇐) ⊗₁ id)          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    α⇒ ∘ ((id ⊗₁ cup) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)    ≈⟨ extendʳ assoc-commute-from ⟩
    (id ⊗₁ (cup ⊗₁ id)) ∘ α⇒ ∘ (ρ⇐ ⊗₁ id)    ≈⟨ refl⟩∘⟨ triangle-inv′ ⟩
    (id ⊗₁ (cup ⊗₁ id)) ∘ (id ⊗₁ λ⇐)         ≈⟨ merge₂ˡ ⟩
    id ⊗₁ cup-openˡ cup                      ∎

  -- Two cups planted side by side commute: the one already in place can be
  -- pushed under the one being planted, which then opens on its own unit.
  --
  --       X       Y       A       B
  --       │       │     ┌─┴───────┴─┐
  --       │       │     │   cup′    │
  --     ┌─┴───────┴─┐   └───────────┘
  --     │    cup    │
  --     └───────────┘
  --                       ≈
  --       X       Y       A       B
  --     ┌─┴───────┴─┐     │       │
  --     │    cup    │     │       │
  --     └───────────┘   ┌─┴───────┴─┐
  --                     │   cup′    │
  --                     └───────────┘

  parallel-cups-commute : {cup : unit ⇒ X ⊗₀ Y} {cup′ : unit ⇒ A ⊗₀ B} →
    (id ⊗₁ cup-openʳ cup′) ∘ cup ≈ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′
  parallel-cups-commute {cup = cup} {cup′} = begin
    (id ⊗₁ cup-openʳ cup′) ∘ cup        ≈˘⟨ cup-openʳ-natural ⟩∘⟨refl ⟩
    (α⇒ ∘ cup-openʳ cup′) ∘ cup          ≈⟨ pullʳ (⟺ (cup-openʳ-commute cup′)) ⟩
    α⇒ ∘ (cup ⊗₁ id) ∘ cup-openʳ cup′    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ open-unit ⟩
    α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′        ∎
    where
      open-unit : cup-openʳ {A = unit} cup′ ≈ λ⇐ ∘ cup′
      open-unit = begin
        (id ⊗₁ cup′) ∘ ρ⇐  ≈⟨ refl⟩∘⟨ ⟺ coherence-inv₃ ⟩
        (id ⊗₁ cup′) ∘ λ⇐  ≈˘⟨ unitorˡ-commute-to ⟩
        λ⇐ ∘ cup′          ∎

  -- The pentagon, in cap vocabulary: a cap on `C ⊗₀ X` closed against `A ⊗₀ B`,
  -- once the two associators in front of it are unwound, is that cap closed
  -- against `B` alone.  Again `A` only watches.
  cap-closeʳ-pentagon : {cap : C ⊗₀ X ⇒ unit} →
    cap-closeʳ {A = A ⊗₀ B} cap ∘ α⇒ ∘ (α⇐ ⊗₁ id {X})
    ≈ (id ⊗₁ cap-bendʳ cap) ∘ α⇒
  cap-closeʳ-pentagon {cap = cap} = begin
    cap-closeʳ cap ∘ α⇒ ∘ (α⇐ ⊗₁ id)                 ≈⟨ pushˡ cap-closeʳ-assoc ⟩
    (id ⊗₁ cap-closeʳ cap) ∘ α⇒ ∘ α⇒ ∘ (α⇐ ⊗₁ id)    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    (id ⊗₁ cap-closeʳ cap) ∘ (α⇒ ∘ α⇒) ∘ (α⇐ ⊗₁ id)  ≈⟨ refl⟩∘⟨ pentagon-collapse ⟩
    (id ⊗₁ cap-closeʳ cap) ∘ (id ⊗₁ α⇒) ∘ α⇒         ≈⟨ pullˡ merge₂ˡ ⟩
    (id ⊗₁ cap-bendʳ cap) ∘ α⇒                       ∎

  cup-bendˡ-assoc : (cup : unit ⇒ X ⊗₀ Y) →
    (id ⊗₁ α⇒) ∘ α⇒ ∘ (cup-bendˡ {A = A} cup ⊗₁ id {B})
    ≈ cup-bendˡ cup
  cup-bendˡ-assoc cup = begin
    (id ⊗₁ α⇒) ∘ α⇒ ∘ (cup-bendˡ cup ⊗₁ id)         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
    (id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘
      (cup-openˡ cup ⊗₁ id)                         ≈⟨ assoc²εβ ⟩
    ((id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id)) ∘
      (cup-openˡ cup ⊗₁ id)                         ≈⟨ pentagon ⟩∘⟨refl ⟩
    (α⇒ ∘ α⇒) ∘ (cup-openˡ cup ⊗₁ id)               ≈⟨ pullʳ cup-openˡ-natural ⟩
    cup-bendˡ cup                                   ∎

  cap-bendˡ-assoc : (cap : X ⊗₀ Y ⇒ unit) →
    (cap-bendˡ {A = A} cap ⊗₁ id {B}) ∘ α⇐ ∘ (id ⊗₁ α⇐)
    ≈ cap-bendˡ cap
  cap-bendˡ-assoc cap = begin
    ((cap-closeˡ cap ∘ α⇐) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)  ≈⟨ pushˡ split₁ˡ ⟩
    (cap-closeˡ cap ⊗₁ id) ∘ (α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)
      ≈⟨ pushˡ (⟺ cap-closeˡ-natural) ⟩
    cap-closeˡ cap ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)
      ≈⟨ refl⟩∘⟨ assoc²εβ ⟩
    cap-closeˡ cap ∘ (α⇒ ∘ (α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)
      ≈⟨ refl⟩∘⟨ pentagon-assoc ⟩∘⟨refl ⟩
    cap-closeˡ cap ∘ (α⇐ ∘ (id ⊗₁ α⇒)) ∘ (id ⊗₁ α⇐)
      ≈⟨ refl⟩∘⟨ cancelʳ (⊗-cancel identity² associator.isoʳ) ⟩
    cap-bendˡ cap                                           ∎

  -- Closing `cap` on the left of the inner pair, with `λ⇒`, is the same as
  -- reassociating first and closing it on the right, with `ρ⇒`.  This is the
  -- triangle, whiskered on both sides by `A` and `X`.
  cap-reassoc : {cap : B ⊗₀ C ⇒ unit} →
    (id {A} ⊗₁ cap-bendˡ {A = X} cap) ∘ α⇒ ≈ (cap-bendʳ cap ⊗₁ id) ∘ α⇐
  cap-reassoc {cap = cap} = begin
    (id ⊗₁ ((λ⇒ ∘ (cap ⊗₁ id)) ∘ α⇐)) ∘ α⇒                   ≈⟨ (refl⟩⊗⟨ assoc) ⟩∘⟨refl ⟩
    (id ⊗₁ (λ⇒ ∘ (cap ⊗₁ id) ∘ α⇐)) ∘ α⇒                     ≈⟨ split₂³ ⟩∘⟨refl ⟩
    ((id ⊗₁ λ⇒) ∘ (id ⊗₁ (cap ⊗₁ id)) ∘ (id ⊗₁ α⇐)) ∘ α⇒     ≈⟨ assoc²βε ⟩
    (id ⊗₁ λ⇒) ∘ (id ⊗₁ (cap ⊗₁ id)) ∘ (id ⊗₁ α⇐) ∘ α⇒       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-to-coherence ⟩
    (id ⊗₁ λ⇒) ∘ (id ⊗₁ (cap ⊗₁ id)) ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐  ≈⟨ refl⟩∘⟨ extendʳ (⟺ assoc-commute-from) ⟩
    (id ⊗₁ λ⇒) ∘ α⇒ ∘ ((id ⊗₁ cap) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ α⇐  ≈⟨ pullˡ triangle ⟩
    (ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ α⇐       ≈⟨ assoc²εβ ⟩
    ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ α⇐     ≈⟨ merge₁³ ⟩∘⟨refl ⟩
    ((ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇒) ⊗₁ id) ∘ α⇐                     ≈⟨ (sym-assoc ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    (cap-bendʳ cap ⊗₁ id) ∘ α⇐                               ∎

  -- Pentagon slide: given a unit-map `u` and a map `f` whose target splits as
  -- `X ⊗₀ Y`, pull the "cup" built by `u` then `f` leftward through the associators.
  cup-slideˡ : {u : unit ⇒ A ⊗₀ B} {f : B ⇒ X ⊗₀ Y} →
    unit-conjˡ ((α⇐ ⊗₁ id {C}) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id))
    ≈ ((α⇐ ∘ (id ⊗₁ (α⇒ ∘ (f ⊗₁ id)))) ∘ (α⇒ ∘ (u ⊗₁ id))) ∘ λ⇐
  cup-slideˡ {A = A} {C = C} {u = u} {f = f} = pullˡ slide
    where
      -- The slide itself, with the trailing `λ⇐` peeled off.
      slide : α⇒ ∘ (α⇐ ⊗₁ id {C}) ∘ ((id {A} ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id)
           ≈ (α⇐ ∘ (id ⊗₁ (α⇒ ∘ (f ⊗₁ id)))) ∘ (α⇒ ∘ (u ⊗₁ id))
      slide = begin
        α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id)           ≈⟨ pullˡ assoc-from-coherence ⟩
        (α⇐ ∘ (id ⊗₁ α⇒) ∘ α⇒) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id)    ≈⟨ sym-assoc ⟩∘⟨refl ⟩
        ((α⇐ ∘ (id ⊗₁ α⇒)) ∘ α⇒) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id)  ≈⟨ center assoc-commute-from ⟩
        (α⇐ ∘ (id ⊗₁ α⇒)) ∘ ((id ⊗₁ (f ⊗₁ id)) ∘ α⇒) ∘ (u ⊗₁ id)  ≈⟨ refl⟩∘⟨ assoc ⟩
        (α⇐ ∘ (id ⊗₁ α⇒)) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ α⇒ ∘ (u ⊗₁ id)    ≈⟨ center merge₂ˡ ⟩
        α⇐ ∘ (id ⊗₁ (α⇒ ∘ (f ⊗₁ id))) ∘ α⇒ ∘ (u ⊗₁ id)            ≈⟨ sym-assoc ⟩
        (α⇐ ∘ (id ⊗₁ (α⇒ ∘ (f ⊗₁ id)))) ∘ (α⇒ ∘ (u ⊗₁ id))        ∎

  -- Slide a cap `g` sitting in left-tensor position rightward through the
  -- associators.  Pure associator gymnastics — `g` is treated opaquely.
  cap-slideʳ : {g : B ⊗₀ (C ⊗₀ X) ⇒ Y} →
    (((id {A} ⊗₁ g) ∘ α⇒) ⊗₁ id {Z}) ∘ α⇐ ∘ (id ⊗₁ α⇐)
    ≈ α⇐ ∘ (id ⊗₁ ((g ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))) ∘ α⇒
  cap-slideʳ {C = C} {X = X} {Z = Z} {g = g} = begin
    (((id ⊗₁ g) ∘ α⇒) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)              ≈⟨ split₁ʳ ⟩∘⟨refl ⟩
    (((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ α⇐)      ≈⟨ switch-fromtoˡ associator slide ⟩
    α⇐ ∘ (id ⊗₁ ((g ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))) ∘ α⇒         ∎
    where
      reassociate :
        α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐ {C} {X} {Z})
        ≈ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ α⇐)) ∘ α⇒
      reassociate = begin
        α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)                ≈⟨ assoc²εβ ⟩
        (α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)              ≈˘⟨ assoc-to-coherence ⟩∘⟨refl ⟩
        ((id ⊗₁ α⇐) ∘ α⇒) ∘ (id ⊗₁ α⇐)                   ≈⟨ pullʳ α⇒-id⊗-commute ⟩
        (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ α⇐)) ∘ α⇒             ∎

      merge :
        (id ⊗₁ (g ⊗₁ id)) ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ α⇐)) ∘ α⇒
        ≈ (id ⊗₁ ((g ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))) ∘ α⇒
      merge = ⟺ assoc²βε ○ (merge₂³ ⟩∘⟨refl)

      slide : α⇒ ∘ (((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ α⇐ {C} {X} {Z})
            ≈ (id ⊗₁ ((g ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))) ∘ α⇒
      slide = begin
        α⇒ ∘ (((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ α⇐)   ≈⟨ refl⟩∘⟨ assoc ⟩
        α⇒ ∘ ((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)     ≈⟨ extendʳ assoc-commute-from ⟩
        (id ⊗₁ (g ⊗₁ id)) ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)     ≈⟨ refl⟩∘⟨ reassociate ⟩
        (id ⊗₁ (g ⊗₁ id)) ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ α⇐)) ∘ α⇒  ≈⟨ merge ⟩
        (id ⊗₁ ((g ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))) ∘ α⇒                ∎

open Coherence public
