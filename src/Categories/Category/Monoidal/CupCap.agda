{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Category.Monoidal.Core using (Monoidal)

-- Cup and cap calculus in a monoidal category.
-- A cup is a morphism `unit ⇒ Z`, drawn as creating `Z` from no input wires.
-- A cap is a morphism `Z ⇒ unit`, drawn as consuming `Z`.

-- In the delooping view (https://ncatlab.org/nlab/show/delooping+hypothesis),
-- which views a monoidal category as a bicategory on one object, caps and cups are
-- 2-cells that create or consume the 1-cell `Z` from the "identity" 1-cell `unit`.

module Categories.Category.Monoidal.CupCap
  {o ℓ e} {𝒞 : Category o ℓ e} (M : Monoidal 𝒞) where

open Category 𝒞
open Monoidal M

open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Morphism.Reasoning 𝒞

open Shorthands

private
  variable
    A B C D E W X Y Z : Obj

-- Opening a cup beside a spectator wire, and closing a cap beside one.  A cup
-- `unit ⇒ Z` is introduced against the spectator `A` by an inverse unitor, and a
-- cap `Z ⇒ unit` is absorbed into it by a unitor; the ˡ/ʳ says which side of `A`
-- the cup or cap sits on.  Every cup and cap in sight is built from these.
-- Diagrams read bottom-to-top.
--
--       cup-openˡ cup          cup-openʳ cup          cap-closeʳ cap
--
--       Z       A              A       Z                    A
--     ┌─┴─┐     │              │     ┌─┴─┐                  │
--     │cup│     │              │     │cup│                  │
--     └───┘     │              │     └───┘            A     Z
--               A              A                      │   ┌─┴─┐
--                                                     │   │cap│
--                                                     │   └───┘

cup-openˡ : unit ⇒ Z → A ⇒ Z ⊗₀ A
cup-openˡ cup = (cup ⊗₁ id) ∘ λ⇐

cup-openʳ : unit ⇒ Z → A ⇒ A ⊗₀ Z
cup-openʳ cup = (id ⊗₁ cup) ∘ ρ⇐

cap-closeʳ : Z ⇒ unit → A ⊗₀ Z ⇒ A
cap-closeʳ cap = ρ⇒ ∘ (id ⊗₁ cap)

cup-bendˡ : unit ⇒ X ⊗₀ Y → A ⇒ X ⊗₀ (Y ⊗₀ A)
cup-bendˡ cup = α⇒ ∘ cup-openˡ cup

-- A cap on a *pair* has to reassociate first to reach its two wires.  Bending
-- `cap : Z ⊗₀ B ⇒ unit` around a spectator `A` on the right is `cap-bendˡ`; the
-- corresponding right-handed bend is `cap-closeʳ cap ∘ α⇒`, and `cap-reassoc`
-- below says the two agree.

cap-bendˡ : Z ⊗₀ B ⇒ unit → Z ⊗₀ (B ⊗₀ A) ⇒ A
cap-bendˡ cap = λ⇒ ∘ (cap ⊗₁ id) ∘ α⇐

cup-nest : unit ⇒ X ⊗₀ W → unit ⇒ Y ⊗₀ Z → unit ⇒ (X ⊗₀ Y) ⊗₀ (Z ⊗₀ W)
cup-nest cup cup′ = α⇐ ∘ (id ⊗₁ cup-bendˡ cup′) ∘ cup

-- `cup′` is planted inside `cup`; hence the output order `X`, `Y`, `Z`, `W`.
--
--       X       Y       Z       W
--       │     ┌─┴───────┴─┐     │
--       │     │   cup′    │     │
--       │     └───────────┘     │
--     ┌─┴───────────────────────┴──┐
--     │            cup             │
--     └────────────────────────────┘

-- Conjugate a morphism by a unitor and the associator.  `unit-conjˡ f` feeds `f`
-- a unit on the left (via `λ⇐`) and reassociates its output to the right;
-- `unit-conjʳ` mirrors it on the right (via `ρ⇐`).  A cup bent into place is
-- exactly one of these applied to a whiskered cup: `unit-conjˡ (cup ⊗₁ id)` is
-- `α⇒ ∘ cup-openˡ cup`, and `unit-conjʳ (id ⊗₁ cup)` is `α⇐ ∘ cup-openʳ cup`.

unit-conjˡ : (unit ⊗₀ D ⇒ (A ⊗₀ B) ⊗₀ C) → (D ⇒ A ⊗₀ (B ⊗₀ C))
unit-conjˡ f = α⇒ ∘ f ∘ λ⇐

unit-conjʳ : (D ⊗₀ unit ⇒ A ⊗₀ (B ⊗₀ C)) → (D ⇒ (A ⊗₀ B) ⊗₀ C)
unit-conjʳ f = α⇐ ∘ f ∘ ρ⇐

-- A morphism on the spectator wire commutes through a right cap.
cap-closeʳ-commute : (cap : Z ⇒ unit) {f : A ⇒ B} →
  cap-closeʳ cap ∘ (f ⊗₁ id) ≈ f ∘ cap-closeʳ cap
cap-closeʳ-commute cap {f = f} = begin
  (ρ⇒ ∘ (id ⊗₁ cap)) ∘ (f ⊗₁ id)  ≈⟨ pullʳ (⟺ whisker-comm) ⟩
  ρ⇒ ∘ (f ⊗₁ id) ∘ (id ⊗₁ cap)    ≈⟨ extendʳ unitorʳ-commute-from ⟩
  f ∘ cap-closeʳ cap                ∎

cap-closeʳ-resp : {A : Obj} {cap cap′ : Z ⇒ unit} →
  cap ≈ cap′ → cap-closeʳ {A = A} cap ≈ cap-closeʳ cap′
cap-closeʳ-resp {A = A} cap≈cap′ = refl⟩∘⟨ (refl⟩⊗⟨ cap≈cap′)

-- Close after a map on the cap's wire by composing that map into the cap.
cap-closeʳ-compose : (cap : Z ⇒ unit) {f : Y ⇒ Z} →
  cap-closeʳ cap ∘ (id {A} ⊗₁ f) ≈ cap-closeʳ (cap ∘ f)
cap-closeʳ-compose cap {f = f} = pullʳ merge₂ˡ

-- The same, for the right-handed bend.
cap-bendʳ-commute : (cap : Y ⊗₀ Z ⇒ unit) {f : A ⇒ B} →
  (cap-closeʳ cap ∘ α⇒) ∘ ((f ⊗₁ id {Y}) ⊗₁ id {Z}) ≈ f ∘ cap-closeʳ cap ∘ α⇒
cap-bendʳ-commute cap {f = f} = begin
  (cap-closeʳ cap ∘ α⇒) ∘ ((f ⊗₁ id) ⊗₁ id)  ≈⟨ pullʳ α⇒-⊗id-commute ⟩
  cap-closeʳ cap ∘ (f ⊗₁ id) ∘ α⇒            ≈⟨ extendʳ (cap-closeʳ-commute cap) ⟩
  f ∘ cap-closeʳ cap ∘ α⇒                    ∎

-- `A` is a spectator: opening a cup on `A ⊗₀ B` opens it on `B`, and closing a
-- cap on `A ⊗₀ B` closes it on `B`.  Only the associator notices.

cup-openʳ-natural : {cup : unit ⇒ Z} →
  α⇒ {A} {B} {Z} ∘ cup-openʳ cup ≈ id ⊗₁ cup-openʳ cup
cup-openʳ-natural {cup = cup} = begin
  α⇒ ∘ (id ⊗₁ cup) ∘ ρ⇐             ≈˘⟨ refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
  α⇒ ∘ ((id ⊗₁ id) ⊗₁ cup) ∘ ρ⇐     ≈⟨ extendʳ assoc-commute-from ⟩
  (id ⊗₁ (id ⊗₁ cup)) ∘ α⇒ ∘ ρ⇐     ≈˘⟨ refl⟩∘⟨ ρ⇐-assoc ⟩
  (id ⊗₁ (id ⊗₁ cup)) ∘ (id ⊗₁ ρ⇐)  ≈⟨ merge₂ˡ ⟩
  id ⊗₁ cup-openʳ cup               ∎

cap-closeʳ-natural : {cap : Z ⇒ unit} →
  cap-closeʳ {A = A ⊗₀ B} cap ∘ α⇐ {A} {B} {Z} ≈ id ⊗₁ cap-closeʳ cap
cap-closeʳ-natural {cap = cap} = begin
  cap-closeʳ cap ∘ α⇐               ≈⟨ assoc ⟩
  ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇐             ≈⟨ refl⟩∘⟨ α⇐-id⊗-commute ⟩
  ρ⇒ ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ cap))     ≈⟨ pullˡ ρ⇒-assoc ⟩
  (id ⊗₁ ρ⇒) ∘ (id ⊗₁ (id ⊗₁ cap))  ≈⟨ merge₂ˡ ⟩
  id ⊗₁ cap-closeʳ cap              ∎

-- The same fact, with the associator moved to the other side.
cap-closeʳ-assoc : {cap : Z ⇒ unit} →
  cap-closeʳ {A = A ⊗₀ B} cap ≈ (id ⊗₁ cap-closeʳ cap) ∘ α⇒ {A} {B} {Z}
cap-closeʳ-assoc {cap = cap} = begin
  cap-closeʳ cap                ≈˘⟨ cancelʳ associator.isoˡ ⟩
  (cap-closeʳ cap ∘ α⇐) ∘ α⇒    ≈⟨ cap-closeʳ-natural ⟩∘⟨refl ⟩
  (id ⊗₁ cap-closeʳ cap) ∘ α⇒   ∎

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
parallel-cups-commute : {cup : unit ⇒ X ⊗₀ Z} {cup′ : unit ⇒ A ⊗₀ W} →
  (id ⊗₁ cup-openʳ cup′) ∘ cup ≈ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′
parallel-cups-commute {cup = cup} {cup′} = begin
  (id ⊗₁ cup-openʳ cup′) ∘ cup            ≈˘⟨ cup-openʳ-natural ⟩∘⟨refl ⟩
  (α⇒ ∘ (id ⊗₁ cup′) ∘ ρ⇐) ∘ cup          ≈⟨ assoc²βε ⟩
  α⇒ ∘ (id ⊗₁ cup′) ∘ ρ⇐ ∘ cup            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorʳ-commute-to ⟩
  α⇒ ∘ (id ⊗₁ cup′) ∘ (cup ⊗₁ id) ∘ ρ⇐    ≈⟨ refl⟩∘⟨ pullˡ (⟺ whisker-comm) ⟩
  α⇒ ∘ ((cup ⊗₁ id) ∘ (id ⊗₁ cup′)) ∘ ρ⇐  ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ (cup ⊗₁ id) ∘ (id ⊗₁ cup′) ∘ ρ⇐    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ ⟩
  α⇒ ∘ (cup ⊗₁ id) ∘ (id ⊗₁ cup′) ∘ λ⇐    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ unitorˡ-commute-to ⟩
  α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′            ∎

-- The pentagon, in cap vocabulary: a cap on `C ⊗₀ D` closed against `A ⊗₀ B`,
-- once the two associators in front of it are unwound, is that cap closed
-- against `B` alone.  Again `A` only watches.
cap-closeʳ-pentagon : {cap : C ⊗₀ D ⇒ unit} →
  cap-closeʳ {A = A ⊗₀ B} cap ∘ α⇒ ∘ (α⇐ ⊗₁ id {D})
  ≈ (id ⊗₁ (cap-closeʳ cap ∘ α⇒)) ∘ α⇒
cap-closeʳ-pentagon {cap = cap} = begin
  cap-closeʳ cap ∘ α⇒ ∘ (α⇐ ⊗₁ id)                 ≈⟨ cap-closeʳ-assoc ⟩∘⟨refl ⟩
  ((id ⊗₁ cap-closeʳ cap) ∘ α⇒) ∘ α⇒ ∘ (α⇐ ⊗₁ id)  ≈⟨ assoc ⟩
  (id ⊗₁ cap-closeʳ cap) ∘ α⇒ ∘ α⇒ ∘ (α⇐ ⊗₁ id)    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  (id ⊗₁ cap-closeʳ cap) ∘ (α⇒ ∘ α⇒) ∘ (α⇐ ⊗₁ id)  ≈⟨ refl⟩∘⟨ pentagon-collapse ⟩
  (id ⊗₁ cap-closeʳ cap) ∘ (id ⊗₁ α⇒) ∘ α⇒         ≈⟨ pullˡ merge₂ˡ ⟩
  (id ⊗₁ (cap-closeʳ cap ∘ α⇒)) ∘ α⇒               ∎

cup-bendˡ-assoc : (cup : unit ⇒ X ⊗₀ Y) →
  (id ⊗₁ α⇒) ∘ α⇒ ∘ (cup-bendˡ {A = A} cup ⊗₁ id {B})
  ≈ cup-bendˡ cup
cup-bendˡ-assoc cup = begin
  (id ⊗₁ α⇒) ∘ α⇒ ∘ (cup-bendˡ cup ⊗₁ id)                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁³ ⟩
  (id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘ ((cup ⊗₁ id) ⊗₁ id)
    ∘ (λ⇐ ⊗₁ id)                                         ≈˘⟨ assoc²βε ⟩
  ((id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id)) ∘ ((cup ⊗₁ id) ⊗₁ id)
    ∘ (λ⇐ ⊗₁ id)                                         ≈⟨ pentagon ⟩∘⟨refl ⟩
  (α⇒ ∘ α⇒) ∘ ((cup ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)           ≈⟨ assoc ⟩
  α⇒ ∘ α⇒ ∘ ((cup ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)             ≈⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
  α⇒ ∘ (cup ⊗₁ (id ⊗₁ id)) ∘ α⇒ ∘ (λ⇐ ⊗₁ id)             ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
  α⇒ ∘ (cup ⊗₁ id) ∘ α⇒ ∘ (λ⇐ ⊗₁ id)                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ λ⇐-assoc ⟩
  cup-bendˡ cup                                           ∎

-- Closing `cap` on the left of the inner pair, with `λ⇒`, is the same as
-- reassociating first and closing it on the right, with `ρ⇒`.  This is the
-- triangle, whiskered on both sides by `A` and `D`.
cap-reassoc : {cap : B ⊗₀ C ⇒ unit} →
  (id {A} ⊗₁ cap-bendˡ {A = D} cap) ∘ α⇒ ≈ ((cap-closeʳ cap ∘ α⇒) ⊗₁ id) ∘ α⇐
cap-reassoc {cap = cap} = begin
  (id ⊗₁ (λ⇒ ∘ (cap ⊗₁ id) ∘ α⇐)) ∘ α⇒                     ≈⟨ split₂³ ⟩∘⟨refl ⟩
  ((id ⊗₁ λ⇒) ∘ (id ⊗₁ (cap ⊗₁ id)) ∘ (id ⊗₁ α⇐)) ∘ α⇒     ≈⟨ assoc²βε ⟩
  (id ⊗₁ λ⇒) ∘ (id ⊗₁ (cap ⊗₁ id)) ∘ (id ⊗₁ α⇐) ∘ α⇒       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-to-coherence ⟩
  (id ⊗₁ λ⇒) ∘ (id ⊗₁ (cap ⊗₁ id)) ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐  ≈⟨ refl⟩∘⟨ extendʳ (⟺ assoc-commute-from) ⟩
  (id ⊗₁ λ⇒) ∘ α⇒ ∘ ((id ⊗₁ cap) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ α⇐  ≈⟨ pullˡ triangle ⟩
  (ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ α⇐       ≈˘⟨ assoc²βε ⟩
  ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ α⇐     ≈˘⟨ split₁³ ⟩∘⟨refl ⟩
  ((ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇒) ⊗₁ id) ∘ α⇐                     ≈˘⟨ (assoc ⟩⊗⟨refl) ⟩∘⟨refl ⟩
  ((cap-closeʳ cap ∘ α⇒) ⊗₁ id) ∘ α⇐                       ∎

-- Pentagon slide: given a unit-map `u` and a map `f` whose target splits as
-- `X ⊗₀ Y`, pull the "cup" built by `u` then `f` leftward through the associators.
cup-slideˡ : {u : unit ⇒ A ⊗₀ B} {f : B ⇒ X ⊗₀ Y} →
  unit-conjˡ ((α⇐ ⊗₁ id {E}) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id))
  ≈ ((α⇐ ∘ (id ⊗₁ (α⇒ ∘ (f ⊗₁ id)))) ∘ (α⇒ ∘ (u ⊗₁ id))) ∘ λ⇐
cup-slideˡ {A = A} {E = E} {u = u} {f = f} = begin
  α⇒ ∘ ((α⇐ ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id)) ∘ λ⇐      ≈⟨ sym-assoc ⟩
  (α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id)) ∘ λ⇐      ≈⟨ slide ⟩∘⟨refl ⟩
  ((α⇐ ∘ (id ⊗₁ (α⇒ ∘ (f ⊗₁ id)))) ∘ (α⇒ ∘ (u ⊗₁ id))) ∘ λ⇐   ∎
  where
    -- The slide itself, with the trailing `λ⇐` peeled off.
    slide : α⇒ ∘ (α⇐ ⊗₁ id {E}) ∘ ((id {A} ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id)
         ≈ (α⇐ ∘ (id ⊗₁ (α⇒ ∘ (f ⊗₁ id)))) ∘ (α⇒ ∘ (u ⊗₁ id))
    slide = begin
      α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id)           ≈⟨ pullˡ assoc-from-coherence ⟩
      (α⇐ ∘ (id ⊗₁ α⇒) ∘ α⇒) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id)    ≈˘⟨ assoc ⟩∘⟨refl ⟩
      ((α⇐ ∘ (id ⊗₁ α⇒)) ∘ α⇒) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (u ⊗₁ id)  ≈⟨ center assoc-commute-from ⟩
      (α⇐ ∘ (id ⊗₁ α⇒)) ∘ ((id ⊗₁ (f ⊗₁ id)) ∘ α⇒) ∘ (u ⊗₁ id)  ≈⟨ refl⟩∘⟨ assoc ⟩
      (α⇐ ∘ (id ⊗₁ α⇒)) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ α⇒ ∘ (u ⊗₁ id)    ≈⟨ center merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ (α⇒ ∘ (f ⊗₁ id))) ∘ α⇒ ∘ (u ⊗₁ id)            ≈⟨ sym-assoc ⟩
      (α⇐ ∘ (id ⊗₁ (α⇒ ∘ (f ⊗₁ id)))) ∘ (α⇒ ∘ (u ⊗₁ id))        ∎

-- Slide a cap `g` sitting in left-tensor position rightward through the
-- associators.  Pure associator gymnastics — `g` is treated opaquely.
cap-slideʳ : {g : B ⊗₀ (C ⊗₀ D) ⇒ E} →
  (((id {A} ⊗₁ g) ∘ α⇒) ⊗₁ id {X}) ∘ α⇐ ∘ (id ⊗₁ α⇐)
  ≈ α⇐ ∘ (id ⊗₁ ((g ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))) ∘ α⇒
cap-slideʳ {C = C} {D = D} {X = X} {g = g} = begin
  (((id ⊗₁ g) ∘ α⇒) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)              ≈⟨ split₁ʳ ⟩∘⟨refl ⟩
  (((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ α⇐)      ≈⟨ switch-fromtoˡ associator slide ⟩
  α⇐ ∘ (id ⊗₁ ((g ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))) ∘ α⇒         ∎
  where
    -- The slide itself, with the leading `α⇐` switched over to an `α⇒`: whisker
    -- `g` off with `assoc-commute-from`, collapse the associator window with
    -- `assoc-to-coherence`, and fold the three whiskered factors back up.
    slide : α⇒ ∘ (((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ α⇐ {C} {D} {X})
          ≈ (id ⊗₁ ((g ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))) ∘ α⇒
    slide = begin
      α⇒ ∘ (((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ α⇐)   ≈⟨ refl⟩∘⟨ assoc ⟩
      α⇒ ∘ ((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)     ≈⟨ extendʳ assoc-commute-from ⟩
      (id ⊗₁ (g ⊗₁ id)) ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)     ≈⟨ refl⟩∘⟨ assoc²εβ ⟩
      (id ⊗₁ (g ⊗₁ id)) ∘ (α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)   ≈˘⟨ refl⟩∘⟨ assoc-to-coherence ⟩∘⟨refl ⟩
      (id ⊗₁ (g ⊗₁ id)) ∘ ((id ⊗₁ α⇐) ∘ α⇒) ∘ (id ⊗₁ α⇐)        ≈⟨ refl⟩∘⟨ pullʳ α⇒-id⊗-commute ⟩
      (id ⊗₁ (g ⊗₁ id)) ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ α⇐)) ∘ α⇒  ≈˘⟨ assoc²βε ⟩
      ((id ⊗₁ (g ⊗₁ id)) ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ α⇐))) ∘ α⇒
        ≈˘⟨ split₂³ ⟩∘⟨refl ⟩
      (id ⊗₁ ((g ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))) ∘ α⇒                ∎
