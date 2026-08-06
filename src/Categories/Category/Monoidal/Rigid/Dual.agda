{-# OPTIONS --without-K --safe #-}

-- Transpose (mate) operations for a left rigid monoidal category:
-- turning cups `unit ⇒ X ⊗₀ Z` and caps `W ⊗₀ X ⇒ unit` into maps out of / into
-- the dual `X ⁻¹` (`cupᵀ`, `capᵀ`, `dual₁`), with their snake and cancellation laws.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)
open import Categories.Functor using (Functor)

module Categories.Category.Monoidal.Rigid.Dual
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C) (L : LeftRigid M) where

open Category C
  using (Obj; _⇒_; _≈_; id; _∘_; assoc; sym-assoc; identityˡ; identityʳ)
open LeftRigid L

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Morphism.Reasoning C
open import Categories.Morphism C using (_≅_)
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)
open import Categories.Category.Monoidal.Properties M
  using (coherence₁; coherence-inv₁; coherence₃)
open import Categories.Category.Monoidal.Reassociation M
  using (α⇐-⊗id-commute; assoc-from-coherence; whisker-comm)
open import Categories.Category.Monoidal.CupCap M

open Shorthands

private
  variable
    W X Y Z : Obj
    f : X ⇒ Y

-- Diagrams read bottom-to-top.  Duality bends a wire: `η` grows a `Y`/`Y ⁻¹` pair
-- out of nothing, `ε` swallows an `X ⁻¹`/`X` pair back into it.  `cupˡ` and `capˡ`
-- are those two bends with a spectator wire alongside.
--
--                cupˡ                                capˡ
--
--     Y       Y ⁻¹      X                                        Y
--     │         │       │                                        │
--     │         │       │                 ╭───────────╮          │
--     ╰─────────╯       │      ← η        │           │          │      ← ε
--                       │                 │           │          │
--                       X               X ⁻¹          X          Y

cupˡ : X ⇒ Y ⊗₀ (Y ⁻¹ ⊗₀ X)
cupˡ = cup-bendˡ η

capˡ : X ⁻¹ ⊗₀ (X ⊗₀ Y) ⇒ Y
capˡ = cap-bendˡ ε

transposeˡ : Z ⊗₀ X ⇒ unit → unit ⇒ X ⊗₀ W → Z ⇒ W
transposeˡ cap cup = cap-bendˡ cap ∘ cup-openʳ cup

cupᵀ : unit ⇒ X ⊗₀ Z → X ⁻¹ ⇒ Z
cupᵀ cup = transposeˡ ε cup

capᵀ : W ⊗₀ X ⇒ unit → W ⇒ X ⁻¹
capᵀ cap = transposeˡ cap η

private
  snake-whiskered : {cup : unit ⇒ X ⊗₀ Z} {cap : Z ⊗₀ X ⇒ unit} →
    ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐ ≈ id →
    (cap-bendʳ cap ⊗₁ id {W}) ∘ α⇐ ∘ cup-openˡ cup ≈ id
  snake-whiskered {cup = cup} {cap} snake = begin
    snakeᵗ ∘ α⇐ ∘ cup-openˡ cup                   ≈⟨ refl⟩∘⟨ glue◽◃ α⇐-⊗id-commute coherence-inv₁ ⟩
    snakeᵗ ∘ (((cup ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id))   ≈⟨ merge₁³ ⟩
    (cap-bendʳ cap ∘ cup-openˡ cup) ⊗₁ id         ≈⟨ assoc²αε ⟩⊗⟨refl ○ ⊗-identityˡ snake ⟩
    id                                            ∎
    where snakeᵗ = cap-bendʳ cap ⊗₁ id

  transposeˡ-cup-cancel : {cup : unit ⇒ X ⊗₀ Z} {cap : Z ⊗₀ X ⇒ unit} {cup′ : unit ⇒ X ⊗₀ W} →
    ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐ ≈ id →
    (id ⊗₁ transposeˡ cap cup′) ∘ cup ≈ cup′
  transposeˡ-cup-cancel {cup = cup} {cap} {cup′} snake = begin
    (id ⊗₁ transposeˡ cap cup′) ∘ cup                       ≈⟨ pushˡ split₂ˡ ⟩
    (id ⊗₁ cap-bendˡ cap) ∘ ((id ⊗₁ cup-openʳ cup′) ∘ cup)  ≈⟨ refl⟩∘⟨ parallel-cups-commute ⟩
    (id ⊗₁ cap-bendˡ cap) ∘ (α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′)  ≈⟨ pullˡ cap-reassoc ⟩
    (snakeᵗ ∘ α⇐) ∘ ((cup ⊗₁ id) ∘ λ⇐ ∘ cup′)               ≈⟨ assoc ○ reassoc-tail₅ ⟩
    (snakeᵗ ∘ α⇐ ∘ cup-openˡ cup) ∘ cup′                    ≈⟨ elimˡ (snake-whiskered snake) ⟩
    cup′                                                    ∎
    where snakeᵗ = cap-bendʳ cap ⊗₁ id

  abstract
    -- The left unitor's square against `ε`, with the |coherence₁| triangle glued on.
    ε-λ : ε {X} ∘ (λ⇒ ⊗₁ id) ≈ λ⇒ ∘ (id ⊗₁ ε) ∘ α⇒
    ε-λ = ⟺ (glue◽◃ unitorˡ-commute-from coherence₁)

    ε-mergeʳ : {cap : W ⊗₀ X ⇒ unit} → (id ⊗₁ ε {X}) ∘ (cap ⊗₁ (id ⊗₁ id)) ≈ cap ⊗₁ ε
    ε-mergeʳ {cap = cap} = begin
      (id ⊗₁ ε) ∘ (cap ⊗₁ (id ⊗₁ id))   ≈⟨ ⊗-distrib-over-∘ ⟨
      (id ∘ cap) ⊗₁ (ε ∘ (id ⊗₁ id))    ≈⟨ identityˡ ⟩⊗⟨ elimʳ ⊗.identity ⟩
      cap ⊗₁ ε                          ∎

    -- `cap` and `ε` land side by side in `unit ⊗₀ unit`; `cap` is the outer one, so
    -- the unitor lets it out in front and leaves `ε` closing against its own wire.
    λ-cap-ε : {cap : W ⊗₀ X ⇒ unit} → λ⇒ ∘ (cap ⊗₁ ε {X}) ≈ cap ∘ cap-closeʳ ε
    λ-cap-ε {cap = cap} = begin
      λ⇒ ∘ (cap ⊗₁ ε)                   ≈⟨ pushʳ serialize₁₂ ⟩
      (λ⇒ ∘ (cap ⊗₁ id)) ∘ (id ⊗₁ ε)    ≈⟨ coherence₃ ⟩∘⟨refl ⟩∘⟨refl ⟩
      (ρ⇒ ∘ (cap ⊗₁ id)) ∘ (id ⊗₁ ε)    ≈⟨ pushˡ unitorʳ-commute-from ⟩
      cap ∘ cap-closeʳ ε                ∎

  -- `transposeˡ cap η` splits at `α⇐` into a head, `λ⇒ ∘ (cap ⊗₁ id) ∘ α⇐`, and a
  -- tail, `cup-openʳ η`.  Whisker the head by `X` and close it with `ε`: the counit
  -- walks left past the associators to meet the cup the tail will plant, and `cap`
  -- drops out in front.  What is left behind it is the snake's cap-half, with `W`
  -- watching.
  ε-against-bendˡ : {cap : W ⊗₀ X ⇒ unit} →
                    ε ∘ (cap-bendˡ cap ⊗₁ id)
                    ≈ cap ∘ (id ⊗₁ cap-bendʳ ε) ∘ α⇒
  ε-against-bendˡ {cap = cap} = begin
    ε ∘ (cap-bendˡ cap ⊗₁ id)                                   ≈⟨ pushʳ (assoc ⟩⊗⟨refl ○ split₁³) ⟩
    (ε ∘ (λ⇒ ⊗₁ id)) ∘ (((cap ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id))       ≈⟨ assoc ○ extendʳ ε-λ ⟩
    λ⇒ ∘ ((id ⊗₁ ε ∘ α⇒) ∘ (((cap ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id)))  ≈⟨ refl⟩∘⟨ assoc-α ⟩
    λ⇒ ∘ (id ⊗₁ ε) ∘ (((cap ⊗₁ (id ⊗₁ id)) ∘ α⇒) ∘ (α⇐ ⊗₁ id))  ≈⟨ refl⟩∘⟨ pull-first ε-mergeʳ ⟩
    λ⇒ ∘ (cap ⊗₁ ε) ∘ α⇒ ∘ (α⇐ ⊗₁ id)                           ≈⟨ λ-cap-⬠ ⟩
    cap ∘ (id ⊗₁ cap-bendʳ ε) ∘ α⇒                              ∎
    where
      assoc-α = center assoc-commute-from
      λ-cap-⬠ = glue◽◃ λ-cap-ε cap-closeʳ-pentagon

  -- Head and tail, glued: the associator hands the tail's cup to the head's cap
  -- (`cup-openʳ-whisker`), the two halves merge under the `W`-whisker, and the
  -- snake straightens them out, leaving `cap` alone.
  transposeˡ-cap-cancel : {cap : W ⊗₀ X ⇒ unit} → ε ∘ (transposeˡ cap η ⊗₁ id) ≈ cap
  transposeˡ-cap-cancel {cap = cap} = begin
    ε ∘ (transposeˡ cap η ⊗₁ id)                          ≈⟨ pushʳ split₁ˡ ⟩
    (ε ∘ (cap-bendˡ cap ⊗₁ id)) ∘ (cup-openʳ η ⊗₁ id)     ≈⟨ ε-against-bendˡ ⟩∘⟨refl ⟩
    (cap ∘ id ⊗₁ cap-bendʳ ε ∘ α⇒) ∘ (cup-openʳ η ⊗₁ id)  ≈⟨ pull-last cup-openʳ-whisker ⟩
    cap ∘ (id ⊗₁ cap-bendʳ ε) ∘ (id ⊗₁ cup-openˡ η)       ≈⟨ refl⟩∘⟨ merge₂ˡ ⟩
    cap ∘ (id ⊗₁ (cap-bendʳ ε ∘ cup-openˡ η))             ≈⟨ elimʳ (refl⟩⊗⟨ snake ○ ⊗.identity) ⟩
    cap                                                   ∎
    where
      snake = assoc²αε ○ snake₁

  abstract
    dual₁-as-cupᵀ : dual₁ f ≈ transposeˡ ε ((f ⊗₁ id) ∘ η)
    dual₁-as-cupᵀ = assoc²εα

    dual₁-as-capᵀ : dual₁ f ≈ transposeˡ (ε ∘ (id ⊗₁ f)) η
    dual₁-as-capᵀ = begin
      dual₁ _                                         ≈⟨ dual₁-as-cupᵀ ⟩
      transposeˡ ε ((_ ⊗₁ id) ∘ η)                    ≈⟨ refl⟩∘⟨ cup-openʳ-∘ η ⟨
      cap-bendˡ ε ∘ (id ⊗₁ (_ ⊗₁ id)) ∘ cup-openʳ η   ≈⟨ pullˡ (cap-bendˡ-⊗ ε) ⟩
      transposeˡ (ε ∘ (id ⊗₁ _)) η                    ∎

-- `dual₁ f : Y ⁻¹ ⇒ X ⁻¹` is `f` bent around: grow an `X`/`X ⁻¹` pair, run `f` on
-- the `X` leg, and close the resulting `Y` against the incoming `Y ⁻¹`.  Reading
-- the two laws below off the picture: sliding `dual₁ f` along the cup (`dual₁-cup`)
-- or the cap (`dual₁-cap`) is the same as sliding `f` the other way.
--
--                              X ⁻¹
--                               │
--         ╭───────────────╮     │
--         │               │     │        ← ε closes Y ⁻¹ against Y
--         │            ┌──┴──┐  │
--         │            │  f  │  │
--         │            └──┬──┘  │
--         │               │     │
--         │               ╰─────╯        ← η grows X / X ⁻¹
--         │
--        Y ⁻¹

abstract
  dual₁-cup : (id ⊗₁ dual₁ f) ∘ η ≈ (f ⊗₁ id) ∘ η
  dual₁-cup {f = f} = begin
    (id ⊗₁ dual₁ f) ∘ η                       ≈⟨ refl⟩⊗⟨ dual₁-as-cupᵀ ⟩∘⟨refl ⟩
    (id ⊗₁ transposeˡ ε ((f ⊗₁ id) ∘ η)) ∘ η  ≈⟨ transposeˡ-cup-cancel snake₁ ⟩
    (f ⊗₁ id) ∘ η                             ∎

  dual₁-cap : ε ∘ (dual₁ f ⊗₁ id) ≈ ε ∘ (id ⊗₁ f)
  dual₁-cap {f = f} = begin
    ε ∘ (dual₁ f ⊗₁ id)                       ≈⟨ refl⟩∘⟨ dual₁-as-capᵀ ⟩⊗⟨refl ⟩
    ε ∘ (transposeˡ (ε ∘ (id ⊗₁ f)) η ⊗₁ id)  ≈⟨ transposeˡ-cap-cancel ⟩
    ε ∘ (id ⊗₁ f)                             ∎

-- Both snake identities survive whiskering by a spectator wire `W`: running the
-- `X`- (resp. `X ⁻¹`-) loop alongside an untouched `W` is still the identity.
-- The snake is the zig-zag pulled straight — bend the wire out with `η`, back in
-- with `ε`, and nothing has happened.
--
--         X                                          X
--         │                                          │
--         │      ╭──────────────╮                    │
--         │      │              │   ← ε              │
--         ╰──────╯              │           =        │
--            ↑ η                │                    │
--                               │                    │
--                               X                    X
--
--     ρ⇒ ∘ (id ⊗₁ ε) ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐   ≈   id          (`snake₁`)

private abstract
  snake₂-whiskered : (cap-closeˡ (ε {X}) ⊗₁ id {W})
      ∘ ((α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐) ⊗₁ id) ≈ id
  snake₂-whiskered = begin
    (cap-closeˡ ε ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐) ⊗₁ id)  ≈⟨ merge₁ˡ ⟩
    (cap-closeˡ ε ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐) ⊗₁ id            ≈⟨ ⊗-identityˡ (assoc ○ snake₂) ⟩
    id                                                    ∎

  cupˡ-expand : α⇐ {W} {X} {X ⁻¹ ⊗₀ Y} ∘ (id ⊗₁ cupˡ)
                ≈ α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)
  cupˡ-expand = begin
    α⇐ ∘ (id ⊗₁ cupˡ)                                 ≈⟨ pushʳ split₂ˡ ⟩
    (α⇐ ∘ (id ⊗₁ α⇒)) ∘ (id ⊗₁ cup-openˡ η)           ≈⟨ pushʳ (⟺ cup-openʳ-whisker) ○ assoc²αδ ⟩
    α⇐ ∘ (((id ⊗₁ α⇒) ∘ α⇒) ∘ (cup-openʳ η ⊗₁ id))    ≈⟨ extendʳ (⟺ assoc-from-coherence) ⟩
    α⇒ ∘ (α⇐ ⊗₁ id) ∘ (cup-openʳ η ⊗₁ id)             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
    α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)  ∎

-- `snake₁`/`snake₂` in `cupˡ`/`capˡ` vocabulary: bending a wire out with `cupˡ`
-- and back in with `capˡ` straightens it, spectator wire and all. `snakeˡ-wire`
-- straightens the wire `X` (with `Y` watching), `snakeˡ-dual` the dual wire `X ⁻¹`
-- (with `W` watching) — the same zig-zag, entered from the other end.
--
--            snakeˡ-wire                          snakeˡ-dual
--
--      X               Y                   X ⁻¹              W
--      │               │                     │               │
--      │   ╭───────╮   │                     │   ╭───────╮   │
--      │   │       │   │   ← capˡ (ε)        │   │       │   │   ← capˡ (ε)
--      ╰───╯       │   │   ← cupˡ (η)        ╰───╯       │   │   ← cupˡ (η)
--                  │   │                                 │   │
--                  X   Y                              X ⁻¹   W
--
-- Read bottom-to-top: the incoming wire climbs the cap's right leg, the cap bends it
-- into its partner, the cup bends it back, and it leaves on the left — a straight
-- wire, drawn crooked.  The spectator never meets either bend.

abstract
  snakeˡ-wire : (id ⊗₁ capˡ {X} {Y}) ∘ cupˡ ≈ id
  snakeˡ-wire = begin
    (id ⊗₁ capˡ) ∘ cupˡ                     ≈⟨ extendʳ cap-reassoc ⟩
    (cap-bendʳ ε ⊗₁ id) ∘ α⇐ ∘ cup-openˡ η  ≈⟨ snake-whiskered snake₁ ⟩
    id                                      ∎

  snakeˡ-dual : capˡ {X} {X ⁻¹ ⊗₀ W} ∘ (id ⊗₁ cupˡ) ≈ id
  snakeˡ-dual = let id⊗η = id ⊗₁ η in begin
    capˡ ∘ (id ⊗₁ cupˡ)                                             ≈⟨ pullʳ cupˡ-expand ⟩
    cap-closeˡ ε ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ (id⊗η ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)      ≈⟨ pullˡ cap-closeˡ-natural ⟩
    (cap-closeˡ ε ⊗₁ id) ∘ (α⇐ ⊗₁ id) ∘ (id⊗η ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)   ≈⟨ refl⟩∘⟨ merge₁³ ⟩
    (cap-closeˡ ε ⊗₁ id) ∘ ((α⇐ ∘ id⊗η ∘ ρ⇐) ⊗₁ id)                 ≈⟨ snake₂-whiskered ⟩
    id                                                              ∎

  cupᵀ-η : (cup : unit ⇒ X ⊗₀ Z) → (id {X} ⊗₁ cupᵀ cup) ∘ η ≈ cup
  cupᵀ-η cup = transposeˡ-cup-cancel snake₁

  cupᵀ-resp-≈ : {cup cup′ : unit ⇒ X ⊗₀ Z} → cup ≈ cup′ → cupᵀ cup ≈ cupᵀ cup′
  cupᵀ-resp-≈ cup≈cup′ = refl⟩∘⟨ refl⟩⊗⟨ cup≈cup′ ⟩∘⟨refl

  cupᵀ-unbend : {f : X ⁻¹ ⇒ Z} → cupᵀ ((id ⊗₁ f) ∘ η) ≈ f
  cupᵀ-unbend {f = f} = begin
    capˡ ∘ cup-openʳ ((id ⊗₁ f) ∘ η)        ≈⟨ refl⟩∘⟨ cup-openʳ-∘ η ⟨
    capˡ ∘ (id ⊗₁ (id ⊗₁ f)) ∘ cup-openʳ η  ≈⟨ pullˡ (cap-bendˡ-commute ε) ⟩
    (f ∘ capˡ) ∘ cup-openʳ η                ≈⟨ cancelʳ (assoc²αε ○ snake₂) ⟩
    f                                       ∎

  cupᵀ-unique : {f g : X ⁻¹ ⇒ Z} → (id ⊗₁ f) ∘ η ≈ (id ⊗₁ g) ∘ η → f ≈ g
  cupᵀ-unique {f = f} {g} f≈g = begin
    f                            ≈⟨ cupᵀ-unbend ⟨
    cupᵀ ((id ⊗₁ f) ∘ η)         ≈⟨ cupᵀ-resp-≈ f≈g ⟩
    cupᵀ ((id ⊗₁ g) ∘ η)         ≈⟨ cupᵀ-unbend ⟩
    g                            ∎

  dual₁-identity : dual₁ (id {X}) ≈ id
  dual₁-identity = dual₁-as-cupᵀ ○ cupᵀ-unbend

  dual₁-resp-≈ : {f g : X ⇒ Y} → f ≈ g → dual₁ f ≈ dual₁ g
  dual₁-resp-≈ {f = f} {g} f≈g = begin
    dual₁ f                       ≈⟨ dual₁-as-cupᵀ ⟩
    cupᵀ ((f ⊗₁ id) ∘ η)          ≈⟨ cupᵀ-resp-≈ (f≈g ⟩⊗⟨refl ⟩∘⟨refl) ⟩
    cupᵀ ((g ⊗₁ id) ∘ η)          ≈⟨ dual₁-as-cupᵀ ⟨
    dual₁ g                       ∎

  private
    dual₁-composite-cup : {f : X ⇒ Y} {g : Y ⇒ Z} →
      (id ⊗₁ (dual₁ f ∘ dual₁ g)) ∘ η ≈ ((g ∘ f) ⊗₁ id) ∘ η
    dual₁-composite-cup {f = f} {g} = begin
      (id ⊗₁ (dual₁ f ∘ dual₁ g)) ∘ η           ≈⟨ pushˡ split₂ˡ ⟩
      (id ⊗₁ dual₁ f) ∘ (id ⊗₁ dual₁ g) ∘ η     ≈⟨ refl⟩∘⟨ dual₁-cup ⟩
      (id ⊗₁ dual₁ f) ∘ (g ⊗₁ id) ∘ η           ≈⟨ extendʳ (⟺ whisker-comm) ⟩
      (g ⊗₁ id) ∘ (id ⊗₁ dual₁ f) ∘ η           ≈⟨ refl⟩∘⟨ dual₁-cup ⟩
      (g ⊗₁ id) ∘ (f ⊗₁ id) ∘ η                 ≈⟨ pullˡ merge₁ˡ ⟩
      ((g ∘ f) ⊗₁ id) ∘ η                       ∎

  dual₁-homomorphism : {f : X ⇒ Y} {g : Y ⇒ Z} → dual₁ (g ∘ f) ≈ dual₁ f ∘ dual₁ g
  dual₁-homomorphism {f = f} {g} = begin
    dual₁ (g ∘ f)                               ≈⟨ dual₁-as-cupᵀ ⟩
    cupᵀ (((g ∘ f) ⊗₁ id) ∘ η)                  ≈⟨ cupᵀ-resp-≈ dual₁-composite-cup ⟨
    cupᵀ ((id ⊗₁ (dual₁ f ∘ dual₁ g)) ∘ η)      ≈⟨ cupᵀ-unbend ⟩
    dual₁ f ∘ dual₁ g                           ∎

dualFunctor : Functor C (Category.op C)
dualFunctor = record
  { F₀           = _⁻¹
  ; F₁           = dual₁
  ; identity     = dual₁-identity
  ; homomorphism = dual₁-homomorphism
  ; F-resp-≈     = dual₁-resp-≈
  }

abstract
  capᵀ-ε : (cap : W ⊗₀ X ⇒ unit) → ε ∘ (capᵀ cap ⊗₁ id) ≈ cap
  capᵀ-ε cap = transposeˡ-cap-cancel

  private
    transposeˡ-resp-≈ : {cap cap′ : Z ⊗₀ X ⇒ unit} {cup : unit ⇒ X ⊗₀ W} →
      cap ≈ cap′ → transposeˡ cap cup ≈ transposeˡ cap′ cup
    transposeˡ-resp-≈ cap≈cap′ = cap-bendˡ-resp cap≈cap′ ⟩∘⟨refl

    -- Precomposition slides into the cap: `g` enters along the spectator wire, walks
    -- left past the cup and the associator, and is absorbed by `cap`.
    transposeˡ-natural : {cap : Z ⊗₀ X ⇒ unit} {cup : unit ⇒ X ⊗₀ W} {g : Y ⇒ Z} →
      transposeˡ cap cup ∘ g ≈ transposeˡ (cap ∘ (g ⊗₁ id)) cup
    transposeˡ-natural {cap = cap} {cup} {g} = begin
      transposeˡ cap cup ∘ g                              ≈⟨ pullʳ (⟺ (cup-openʳ-commute cup)) ⟩
      cap-bendˡ cap ∘ (g ⊗₁ id) ∘ cup-openʳ cup           ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟨
      cap-bendˡ cap ∘ (g ⊗₁ (id ⊗₁ id)) ∘ cup-openʳ cup   ≈⟨ pullˡ (cap-bendˡ-⊗ cap) ⟩
      transposeˡ (cap ∘ (g ⊗₁ id)) cup                    ∎

    -- The two transposes compose into a single one: `capᵀ cap` slides into `cupᵀ`'s
    -- counit (`capᵀ-ε`), leaving `cap` where `ε` was.
    cupᵀ-capᵀ : {cup : unit ⇒ X ⊗₀ Z} {cap : Z ⊗₀ X ⇒ unit} →
      cupᵀ cup ∘ capᵀ cap ≈ λ⇒ ∘ (cap ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ cup) ∘ ρ⇐
    cupᵀ-capᵀ {cup = cup} {cap} = begin
      transposeˡ ε cup ∘ capᵀ cap               ≈⟨ transposeˡ-natural ⟩
      transposeˡ (ε ∘ (capᵀ cap ⊗₁ id)) cup     ≈⟨ transposeˡ-resp-≈ (capᵀ-ε cap) ⟩
      transposeˡ cap cup                        ≈⟨ assoc²αε ⟩
      λ⇒ ∘ (cap ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ cup) ∘ ρ⇐  ∎

  capᵀ-cup : {cup : unit ⇒ X ⊗₀ Z} {cap : Z ⊗₀ X ⇒ unit} →
             ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐ ≈ id →
             (id ⊗₁ capᵀ cap) ∘ cup ≈ η
  capᵀ-cup snake = transposeˡ-cup-cancel snake

------------------------------------------------------------------------------
-- Uniqueness of left duals.
--
-- Two dual structures on the same object give two ways to bend a wire, and the
-- transposes below turn one into the other.  The composites are identities because
-- each is a snake in disguise: bending out with one cup and back with the other's
-- cap leaves a zig-zag, and a zig-zag is a straight wire.
--
--        D ⁻¹                         A
--         │                           │
--         │   ╭──────────╮            │
--         │   │          │  ← ε       │
--         ╰───╯          │      =     │      (`capᵀ`'s cap against `cupᵀ`'s cup)
--            ↑ cup       │            │
--                        │            │
--                        A           D ⁻¹
--
-- If an object `A` is exhibited as a left dual of `D` by a cup/cap pair
-- satisfying the two snake (zig-zag) identities, then `A` is canonically
-- isomorphic to the chosen dual `D ⁻¹` — via the transposes of its cap and cup.
-- Nothing beyond rigidity is needed.  `snakeᴰ` closes the `D`-loop (yielding the
-- other composite through rigidity of `D ⁻¹`) and `snakeᴬ` the `A`-loop.

module _ {D A : Obj}
    (cup : unit ⇒ D ⊗₀ A) (cap : A ⊗₀ D ⇒ unit)
    (snakeᴰ : ρ⇒ ∘ (id {D} ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id {D}) ∘ λ⇐ ≈ id {D})
    (snakeᴬ : λ⇒ ∘ (cap ⊗₁ id {A}) ∘ α⇐ ∘ (id {A} ⊗₁ cup) ∘ ρ⇐ ≈ id {A})
    where

  private abstract
    -- `capᵀ cap ∘ cupᵀ cup` acts trivially on the cup `η`, so it is the identity.
    cupᵀ-capᵀ-η : (id {D} ⊗₁ (capᵀ cap ∘ cupᵀ cup)) ∘ η {D} ≈ η
    cupᵀ-capᵀ-η = begin
      (id ⊗₁ (capᵀ cap ∘ cupᵀ cup)) ∘ η         ≈⟨ pushˡ split₂ˡ ⟩
      (id ⊗₁ capᵀ cap) ∘ (id ⊗₁ cupᵀ cup) ∘ η   ≈⟨ refl⟩∘⟨ cupᵀ-η cup ⟩
      (id ⊗₁ capᵀ cap) ∘ cup                    ≈⟨ capᵀ-cup snakeᴰ ⟩
      η                                         ∎

  dual-uniqueˡ : A ≅ D ⁻¹
  dual-uniqueˡ = record
    { from = capᵀ cap
    ; to   = cupᵀ cup
    ; iso  = record
      { isoˡ = to-from
      ; isoʳ = from-to
      }
    }
    where
      abstract
        to-from : cupᵀ cup ∘ capᵀ cap ≈ id
        to-from = cupᵀ-capᵀ ○ snakeᴬ

        from-to : capᵀ cap ∘ cupᵀ cup ≈ id
        from-to = cupᵀ-unique (cupᵀ-capᵀ-η ○ ⟺ (elimˡ ⊗.identity))
