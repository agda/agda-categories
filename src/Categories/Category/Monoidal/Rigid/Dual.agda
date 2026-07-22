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
  using ( Obj; _⇒_; _≈_; id; _∘_; assoc; sym-assoc; identityˡ; identityʳ
        ; module HomReasoning )
open LeftRigid L

open import Categories.Category.Monoidal.Reasoning M
  using ( _⟩⊗⟨_; refl⟩⊗⟨_; _⟩⊗⟨refl; ⊗-distrib-over-∘
        ; merge₁ʳ; merge₁ˡ; merge₂ˡ; serialize₁₂; serialize₂₁
        ; split₁ˡ; split₁³; split₂ˡ )
open import Categories.Morphism.Reasoning C
  using ( assoc²βε; assoc²εβ; elimʳ; elimˡ; extendʳ; glue◽◃; id-comm
        ; pull-first; pullʳ; pullˡ; pushʳ; pushˡ )
open import Categories.Morphism C using (_≅_)
open import Categories.Category.Monoidal.Utilities M
  using (module Shorthands; triangle-inv′)
open import Categories.Category.Monoidal.Properties M
  using (coherence₁; coherence-inv₁; coherence₃)
open import Categories.Category.Monoidal.Reassociation M
  using (α⇐-⊗id-commute; assoc-from-coherence; whisker-comm)
open import Categories.Category.Monoidal.CupCap M
  using ( cap-bendˡ; cap-closeʳ; cap-closeʳ-pentagon; cap-reassoc
        ; cup-openˡ; cup-openʳ; cup-openʳ-whisker; parallel-cups-commute
        ; unit-conjˡ )

open Shorthands
open HomReasoning

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
cupˡ = unit-conjˡ (η ⊗₁ id)

capˡ : X ⁻¹ ⊗₀ (X ⊗₀ Y) ⇒ Y
capˡ = cap-bendˡ ε

private
  transposeˡ : Z ⊗₀ X ⇒ unit → unit ⇒ X ⊗₀ W → Z ⇒ W
  transposeˡ cap cup = cap-bendˡ cap ∘ cup-openʳ cup

  snake-whiskered : {cup : unit ⇒ X ⊗₀ Z} {cap : Z ⊗₀ X ⇒ unit} →
    ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐ ≈ id →
    ((cap-closeʳ cap ∘ α⇒) ⊗₁ id {W}) ∘ α⇐ ∘ cup-openˡ cup ≈ id
  snake-whiskered {cup = cup} {cap} snake = begin
    snakeᵗ ∘ α⇐ ∘ cup-openˡ cup                         ≈⟨ refl⟩∘⟨ pullˡ α⇐-⊗id-commute ⟩
    snakeᵗ ∘ ((((cup ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ λ⇐)          ≈⟨ refl⟩∘⟨ pullʳ coherence-inv₁ ⟩
    snakeᵗ ∘ (((cup ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id))         ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
    snakeᵗ ∘ (cup-openˡ cup ⊗₁ id)                      ≈⟨ merge₁ˡ ⟩
    ((cap-closeʳ cap ∘ α⇒) ∘ cup-openˡ cup) ⊗₁ id       ≈⟨ assoc ⟩⊗⟨refl ⟩
    (cap-closeʳ cap ∘ α⇒ ∘ cup-openˡ cup) ⊗₁ id         ≈⟨ assoc ⟩⊗⟨refl ⟩
    (ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐) ⊗₁ id    ≈⟨ snake ⟩⊗⟨refl ⟩
    id ⊗₁ id                                            ≈⟨ ⊗.identity ⟩
    id                                                  ∎
    where snakeᵗ = (cap-closeʳ cap ∘ α⇒) ⊗₁ id

  transposeˡ-cup-cancel : {cup : unit ⇒ X ⊗₀ Z} {cap : Z ⊗₀ X ⇒ unit} {cup′ : unit ⇒ X ⊗₀ W} →
    ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐ ≈ id →
    (id ⊗₁ transposeˡ cap cup′) ∘ cup ≈ cup′
  transposeˡ-cup-cancel {cup = cup} {cap} {cup′} snake = begin
    (id ⊗₁ transposeˡ cap cup′) ∘ cup                       ≈⟨ pushˡ split₂ˡ ⟩
    (id ⊗₁ cap-bendˡ cap) ∘ ((id ⊗₁ cup-openʳ cup′) ∘ cup)  ≈⟨ refl⟩∘⟨ parallel-cups-commute ⟩
    (id ⊗₁ cap-bendˡ cap) ∘ (α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′)  ≈⟨ pullˡ cap-reassoc ⟩
    (snakeᵗ ∘ α⇐) ∘ ((cup ⊗₁ id) ∘ λ⇐ ∘ cup′)               ≈⟨ assoc ⟩
    snakeᵗ ∘ α⇐ ∘ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′                   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
    snakeᵗ ∘ α⇐ ∘ cup-openˡ cup ∘ cup′                      ≈˘⟨ assoc²βε ⟩
    (snakeᵗ ∘ α⇐ ∘ cup-openˡ cup) ∘ cup′                    ≈⟨ snake-whiskered snake ⟩∘⟨refl ⟩
    id ∘ cup′                                               ≈⟨ identityˡ ⟩
    cup′                                                    ∎
    where snakeᵗ = (cap-closeʳ cap ∘ α⇒) ⊗₁ id

  -- The left unitor's square against `ε`, with the |coherence₁| triangle glued on.
  ε-λ : ε {X} ∘ (λ⇒ ⊗₁ id) ≈ λ⇒ ∘ (id ⊗₁ ε) ∘ α⇒
  ε-λ = ⟺ (glue◽◃ unitorˡ-commute-from coherence₁)

  ε-mergeʳ : {cap : W ⊗₀ X ⇒ unit} → (id ⊗₁ ε {X}) ∘ (cap ⊗₁ (id ⊗₁ id)) ≈ cap ⊗₁ ε
  ε-mergeʳ {cap = cap} = begin
    (id ⊗₁ ε) ∘ (cap ⊗₁ (id ⊗₁ id))   ≈˘⟨ ⊗-distrib-over-∘ ⟩
    (id ∘ cap) ⊗₁ (ε ∘ (id ⊗₁ id))    ≈⟨ identityˡ ⟩⊗⟨ elimʳ ⊗.identity ⟩
    cap ⊗₁ ε                          ∎

  -- `cap` and `ε` land side by side in `unit ⊗₀ unit`; `cap` is the outer one, so
  -- the unitor lets it out in front and leaves `ε` closing against its own wire.
  λ-cap-ε : {cap : W ⊗₀ X ⇒ unit} → λ⇒ ∘ (cap ⊗₁ ε {X}) ≈ cap ∘ cap-closeʳ ε
  λ-cap-ε {cap = cap} = begin
    λ⇒ ∘ (cap ⊗₁ ε)                 ≈⟨ pushʳ serialize₁₂ ⟩
    (λ⇒ ∘ (cap ⊗₁ id)) ∘ (id ⊗₁ ε)  ≈⟨ (coherence₃ ⟩∘⟨refl) ⟩∘⟨refl ⟩
    (ρ⇒ ∘ (cap ⊗₁ id)) ∘ (id ⊗₁ ε)  ≈⟨ unitorʳ-commute-from ⟩∘⟨refl ⟩
    (cap ∘ ρ⇒) ∘ (id ⊗₁ ε)          ≈⟨ assoc ⟩
    cap ∘ cap-closeʳ ε              ∎

  -- `transposeˡ cap η` splits at `α⇐` into a head, `λ⇒ ∘ (cap ⊗₁ id) ∘ α⇐`, and a
  -- tail, `cup-openʳ η`.  Whisker the head by `X` and close it with `ε`: the counit
  -- walks left past the associators to meet the cup the tail will plant, and `cap`
  -- drops out in front.  What is left behind it is the snake's cap-half, with `W`
  -- watching.
  ε-against-bendˡ : {cap : W ⊗₀ X ⇒ unit} →
    ε ∘ (cap-bendˡ cap ⊗₁ id)
    ≈ cap ∘ (id ⊗₁ (cap-closeʳ ε ∘ α⇒)) ∘ α⇒
  ε-against-bendˡ {cap = cap} = begin
    ε ∘ ((λ⇒ ∘ (cap ⊗₁ id) ∘ α⇐) ⊗₁ id)                       ≈⟨ refl⟩∘⟨ split₁³ ⟩
    ε ∘ (λ⇒ ⊗₁ id) ∘ ((cap ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id)         ≈⟨ pullˡ ε-λ ⟩
    (λ⇒ ∘ (id ⊗₁ ε) ∘ α⇒) ∘ ((cap ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id)  ≈⟨ assoc²βε ⟩
    λ⇒ ∘ (id ⊗₁ ε) ∘ α⇒ ∘ ((cap ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
    λ⇒ ∘ (id ⊗₁ ε) ∘ (cap ⊗₁ (id ⊗₁ id)) ∘ α⇒ ∘ (α⇐ ⊗₁ id)    ≈⟨ refl⟩∘⟨ pullˡ ε-mergeʳ ⟩
    λ⇒ ∘ (cap ⊗₁ ε) ∘ α⇒ ∘ (α⇐ ⊗₁ id)                         ≈⟨ pullˡ λ-cap-ε ⟩
    (cap ∘ cap-closeʳ ε) ∘ α⇒ ∘ (α⇐ ⊗₁ id)                    ≈⟨ assoc ⟩
    cap ∘ cap-closeʳ ε ∘ α⇒ ∘ (α⇐ ⊗₁ id)                      ≈⟨ refl⟩∘⟨ cap-closeʳ-pentagon ⟩
    cap ∘ (id ⊗₁ (cap-closeʳ ε ∘ α⇒)) ∘ α⇒                    ∎

  -- Head and tail, glued: the associator hands the tail's cup to the head's cap
  -- (`cup-openʳ-whisker`), the two halves merge under the `W`-whisker, and the
  -- snake straightens them out, leaving `cap` alone.
  transposeˡ-cap-cancel : {cap : W ⊗₀ X ⇒ unit} → ε ∘ (transposeˡ cap η ⊗₁ id) ≈ cap
  transposeˡ-cap-cancel {cap = cap} = begin
    ε ∘ (transposeˡ cap η ⊗₁ id)                          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    ε ∘ (cap-bendˡ cap ⊗₁ id) ∘ (cup-openʳ η ⊗₁ id)       ≈⟨ pullˡ ε-against-bendˡ ⟩
    (cap ∘ (id ⊗₁ snake-cap) ∘ α⇒) ∘ (cup-openʳ η ⊗₁ id)  ≈⟨ assoc²βε ⟩
    cap ∘ (id ⊗₁ snake-cap) ∘ α⇒ ∘ (cup-openʳ η ⊗₁ id)    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cup-openʳ-whisker ⟩
    cap ∘ (id ⊗₁ snake-cap) ∘ (id ⊗₁ cup-openˡ η)         ≈⟨ refl⟩∘⟨ merge₂ˡ ⟩
    cap ∘ (id ⊗₁ (snake-cap ∘ cup-openˡ η))               ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (assoc ○ assoc ○ snake₁) ⟩
    cap ∘ (id ⊗₁ id)                                      ≈⟨ elimʳ ⊗.identity ⟩
    cap                                                   ∎
    where snake-cap = cap-closeʳ ε ∘ α⇒

  dual₁-as-cup-transpose : dual₁ f ≈ transposeˡ ε ((f ⊗₁ id) ∘ η)
  dual₁-as-cup-transpose = assoc²εβ

  dual₁-as-cap-transpose : dual₁ f ≈ transposeˡ (ε ∘ (id ⊗₁ f)) η
  dual₁-as-cap-transpose {f = f} = begin
    dual₁ f
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
    λ⇒ ∘ (ε ⊗₁ id) ∘ α⇐ ∘ ((id ⊗₁ (f ⊗₁ id)) ∘ (id ⊗₁ η)) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pull-first assoc-commute-to ⟩
    λ⇒ ∘ (ε ⊗₁ id) ∘ ((((id ⊗₁ f) ⊗₁ id) ∘ α⇐) ∘ ((id ⊗₁ η) ∘ ρ⇐))
      ≈⟨ refl⟩∘⟨ pull-first merge₁ʳ ⟩
    λ⇒ ∘ (((ε ∘ (id ⊗₁ f)) ⊗₁ id) ∘ α⇐ ∘ cup-openʳ η)       ≈⟨ assoc²εβ ⟩
    transposeˡ (ε ∘ (id ⊗₁ f)) η                            ∎

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

dual₁-cup : (id ⊗₁ dual₁ f) ∘ η ≈ (f ⊗₁ id) ∘ η
dual₁-cup {f = f} = begin
  (id ⊗₁ dual₁ f) ∘ η                         ≈⟨ refl⟩⊗⟨ dual₁-as-cup-transpose ⟩∘⟨refl ⟩
  (id ⊗₁ transposeˡ ε ((f ⊗₁ id) ∘ η)) ∘ η    ≈⟨ transposeˡ-cup-cancel snake₁ ⟩
  (f ⊗₁ id) ∘ η                               ∎

dual₁-cap : ε ∘ (dual₁ f ⊗₁ id) ≈ ε ∘ (id ⊗₁ f)
dual₁-cap {f = f} = begin
  ε ∘ (dual₁ f ⊗₁ id)                       ≈⟨ refl⟩∘⟨ dual₁-as-cap-transpose ⟩⊗⟨refl ⟩
  ε ∘ (transposeˡ (ε ∘ (id ⊗₁ f)) η ⊗₁ id)  ≈⟨ transposeˡ-cap-cancel ⟩
  ε ∘ (id ⊗₁ f)                             ∎

cupᵀ : unit ⇒ X ⊗₀ Z → X ⁻¹ ⇒ Z
cupᵀ cup = transposeˡ ε cup

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

private
  snake₂-whiskered : ((λ⇒ ⊗₁ id {W}) ∘ ((ε {X} ⊗₁ id) ⊗₁ id))
      ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id) ≈ id
  snake₂-whiskered = begin
    ((λ⇒ ⊗₁ id) ∘ ((ε ⊗₁ id) ⊗₁ id)) ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)
      ≈˘⟨ split₁ˡ ⟩∘⟨ split₁³ ⟩
    ((λ⇒ ∘ (ε ⊗₁ id)) ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐) ⊗₁ id)  ≈⟨ merge₁ˡ ⟩
    ((λ⇒ ∘ (ε ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐) ⊗₁ id            ≈⟨ assoc ⟩⊗⟨refl ⟩
    (λ⇒ ∘ (ε ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐) ⊗₁ id              ≈⟨ snake₂ ⟩⊗⟨refl ⟩
    id ⊗₁ id                                                  ≈⟨ ⊗.identity ⟩
    id                                                        ∎

cupˡ-expand : α⇐ {W} {X} {X ⁻¹ ⊗₀ Y} ∘ (id ⊗₁ cupˡ)
              ≈ α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)
cupˡ-expand = begin
  α⇐ ∘ (id ⊗₁ cupˡ)                                     ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
  α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ ((η ⊗₁ id) ∘ λ⇐))            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩
  α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (η ⊗₁ id)) ∘ (id ⊗₁ λ⇐)      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ triangle-inv′ ⟩
  α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (η ⊗₁ id)) ∘ α⇒ ∘ (ρ⇐ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
  α⇐ ∘ (id ⊗₁ α⇒) ∘ α⇒ ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)   ≈⟨ assoc²εβ ⟩
  (α⇐ ∘ (id ⊗₁ α⇒) ∘ α⇒) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id) ≈˘⟨ assoc-from-coherence ⟩∘⟨refl ⟩
  (α⇒ ∘ (α⇐ ⊗₁ id)) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)      ≈⟨ assoc ⟩
  α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)        ∎

private
  -- `capˡ`'s head, rewhiskered: the counit and its unitor drop onto the left factor.
  capˡ-head : λ⇒ ∘ (ε {X} ⊗₁ id {X ⁻¹ ⊗₀ W}) ∘ α⇒ ≈ (λ⇒ ⊗₁ id) ∘ ((ε ⊗₁ id) ⊗₁ id)
  capˡ-head = begin
    λ⇒ ∘ (ε ⊗₁ id) ∘ α⇒               ≈˘⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
    λ⇒ ∘ (ε ⊗₁ (id ⊗₁ id)) ∘ α⇒       ≈˘⟨ refl⟩∘⟨ assoc-commute-from ⟩
    λ⇒ ∘ α⇒ ∘ ((ε ⊗₁ id) ⊗₁ id)       ≈⟨ pullˡ coherence₁ ⟩
    (λ⇒ ⊗₁ id) ∘ ((ε ⊗₁ id) ⊗₁ id)    ∎

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

snakeˡ-wire : (id ⊗₁ capˡ {X} {Y}) ∘ cupˡ ≈ id
snakeˡ-wire = begin
  (id ⊗₁ capˡ) ∘ cupˡ                               ≈⟨ sym-assoc ⟩
  ((id ⊗₁ capˡ) ∘ α⇒) ∘ cup-openˡ η                 ≈⟨ cap-reassoc ⟩∘⟨refl ⟩
  (((cap-closeʳ ε ∘ α⇒) ⊗₁ id) ∘ α⇐) ∘ cup-openˡ η  ≈⟨ assoc ⟩
  ((cap-closeʳ ε ∘ α⇒) ⊗₁ id) ∘ α⇐ ∘ cup-openˡ η    ≈⟨ snake-whiskered snake₁ ⟩
  id                                                ∎

snakeˡ-dual : capˡ {X} {X ⁻¹ ⊗₀ W} ∘ (id ⊗₁ cupˡ) ≈ id
snakeˡ-dual = begin
  capˡ ∘ (id ⊗₁ cupˡ)                             ≈⟨ assoc²βε ⟩
  λ⇒ ∘ (ε ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ cupˡ)              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cupˡ-expand ⟩
  λ⇒ ∘ (ε ⊗₁ id) ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)
    ≈⟨ assoc²εβ ⟩
  (λ⇒ ∘ (ε ⊗₁ id) ∘ α⇒) ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)
    ≈⟨ capˡ-head ⟩∘⟨refl ⟩
  ((λ⇒ ⊗₁ id) ∘ ((ε ⊗₁ id) ⊗₁ id)) ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)
    ≈⟨ snake₂-whiskered ⟩
  id                                              ∎

cupᵀ-η : (cup : unit ⇒ X ⊗₀ Z) → (id {X} ⊗₁ cupᵀ cup) ∘ η ≈ cup
cupᵀ-η cup = transposeˡ-cup-cancel snake₁

cupᵀ-resp-≈ : {cup cup′ : unit ⇒ X ⊗₀ Z} → cup ≈ cup′ → cupᵀ cup ≈ cupᵀ cup′
cupᵀ-resp-≈ cup≈cup′ = refl⟩∘⟨ refl⟩⊗⟨ cup≈cup′ ⟩∘⟨refl

private
  ε-mergeˡ : {f : X ⁻¹ ⇒ Z} → (ε {X} ⊗₁ id) ∘ ((id ⊗₁ id) ⊗₁ f) ≈ ε ⊗₁ f
  ε-mergeˡ = ⟺ ⊗-distrib-over-∘ ○ (elimʳ ⊗.identity ⟩⊗⟨ identityˡ)

  capˡ-natural : {f : X ⁻¹ ⇒ Z} → λ⇒ ∘ (ε {X} ⊗₁ f) ∘ α⇐ ≈ f ∘ capˡ
  capˡ-natural {f = f} = begin
    λ⇒ ∘ (ε ⊗₁ f) ∘ α⇐                  ≈⟨ refl⟩∘⟨ serialize₂₁ ⟩∘⟨refl ⟩
    λ⇒ ∘ ((id ⊗₁ f) ∘ (ε ⊗₁ id)) ∘ α⇐   ≈⟨ refl⟩∘⟨ assoc ⟩
    λ⇒ ∘ (id ⊗₁ f) ∘ (ε ⊗₁ id) ∘ α⇐     ≈⟨ extendʳ unitorˡ-commute-from ⟩
    f ∘ capˡ                            ∎

  capˡ-snake : {f : X ⁻¹ ⇒ Z} → (f ∘ capˡ) ∘ ((id ⊗₁ η) ∘ ρ⇐) ≈ f ∘ id
  capˡ-snake {f = f} = begin
    (f ∘ capˡ) ∘ ((id ⊗₁ η) ∘ ρ⇐)                       ≈⟨ assoc ⟩
    f ∘ (capˡ ∘ ((id ⊗₁ η) ∘ ρ⇐))                       ≈⟨ refl⟩∘⟨ assoc²βε ⟩
    f ∘ (λ⇒ ∘ (ε ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ η) ∘ ρ⇐)))      ≈⟨ refl⟩∘⟨ snake₂ ⟩
    f ∘ id                                              ∎

cupᵀ-unbend : {f : X ⁻¹ ⇒ Z} → cupᵀ ((id ⊗₁ f) ∘ η) ≈ f
cupᵀ-unbend {f = f} = begin
  cupᵀ ((id ⊗₁ f) ∘ η)                                          ≈⟨ assoc²βε ⟩
  λ⇒ ∘ (ε ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ ((id ⊗₁ f) ∘ η)) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
  λ⇒ ∘ (ε ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ f)) ∘ (id ⊗₁ η) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ assoc-commute-to ⟩
  λ⇒ ∘ (ε ⊗₁ id) ∘ (((id ⊗₁ id) ⊗₁ f) ∘ α⇐) ∘ ((id ⊗₁ η) ∘ ρ⇐)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (ε ⊗₁ id) ∘ ((id ⊗₁ id) ⊗₁ f) ∘ (α⇐ ∘ ((id ⊗₁ η) ∘ ρ⇐))  ≈⟨ refl⟩∘⟨ pullˡ ε-mergeˡ ⟩
  λ⇒ ∘ (ε ⊗₁ f) ∘ (α⇐ ∘ ((id ⊗₁ η) ∘ ρ⇐))                       ≈⟨ assoc²εβ ⟩
  (λ⇒ ∘ (ε ⊗₁ f) ∘ α⇐) ∘ ((id ⊗₁ η) ∘ ρ⇐)                       ≈⟨ capˡ-natural ⟩∘⟨refl ⟩
  (f ∘ capˡ) ∘ ((id ⊗₁ η) ∘ ρ⇐)                                 ≈⟨ capˡ-snake ⟩
  f ∘ id                                                        ≈⟨ identityʳ ⟩
  f                                                             ∎

cupᵀ-unique : {f g : X ⁻¹ ⇒ Z} → (id ⊗₁ f) ∘ η ≈ (id ⊗₁ g) ∘ η → f ≈ g
cupᵀ-unique f≈g = ⟺ cupᵀ-unbend ○ cupᵀ-resp-≈ f≈g ○ cupᵀ-unbend

dual₁-identity : dual₁ (id {X}) ≈ id
dual₁-identity = dual₁-as-cup-transpose ○ cupᵀ-unbend

dual₁-resp-≈ : {f g : X ⇒ Y} → f ≈ g → dual₁ f ≈ dual₁ g
dual₁-resp-≈ f≈g = dual₁-as-cup-transpose
  ○ cupᵀ-resp-≈ (f≈g ⟩⊗⟨refl ⟩∘⟨refl) ○ ⟺ dual₁-as-cup-transpose

private
  dual₁-composite-cup : {f : X ⇒ Y} {g : Y ⇒ Z} →
    (id ⊗₁ (dual₁ f ∘ dual₁ g)) ∘ η ≈ ((g ∘ f) ⊗₁ id) ∘ η
  dual₁-composite-cup {f = f} {g} = begin
    (id ⊗₁ (dual₁ f ∘ dual₁ g)) ∘ η             ≈⟨ pushˡ split₂ˡ ⟩
    (id ⊗₁ dual₁ f) ∘ (id ⊗₁ dual₁ g) ∘ η       ≈⟨ refl⟩∘⟨ dual₁-cup ⟩
    (id ⊗₁ dual₁ f) ∘ (g ⊗₁ id) ∘ η             ≈⟨ extendʳ (⟺ whisker-comm) ⟩
    (g ⊗₁ id) ∘ (id ⊗₁ dual₁ f) ∘ η             ≈⟨ refl⟩∘⟨ dual₁-cup ⟩
    (g ⊗₁ id) ∘ (f ⊗₁ id) ∘ η                   ≈⟨ pullˡ merge₁ˡ ⟩
    ((g ∘ f) ⊗₁ id) ∘ η                         ∎

dual₁-homomorphism : {f : X ⇒ Y} {g : Y ⇒ Z} → dual₁ (g ∘ f) ≈ dual₁ f ∘ dual₁ g
dual₁-homomorphism = dual₁-as-cup-transpose ○ cupᵀ-resp-≈ (⟺ dual₁-composite-cup) ○ cupᵀ-unbend

dualFunctor : Functor C (Category.op C)
dualFunctor = record
  { F₀           = _⁻¹
  ; F₁           = dual₁
  ; identity     = dual₁-identity
  ; homomorphism = dual₁-homomorphism
  ; F-resp-≈     = dual₁-resp-≈
  }

capᵀ : W ⊗₀ X ⇒ unit → W ⇒ X ⁻¹
capᵀ cap = transposeˡ cap η

capᵀ-ε : (cap : W ⊗₀ X ⇒ unit) → ε ∘ (capᵀ cap ⊗₁ id) ≈ cap
capᵀ-ε cap = transposeˡ-cap-cancel

private
  transposeˡ-resp-cap : {cap cap′ : Z ⊗₀ X ⇒ unit} {cup : unit ⇒ X ⊗₀ W} →
    cap ≈ cap′ → transposeˡ cap cup ≈ transposeˡ cap′ cup
  transposeˡ-resp-cap cap≈cap′ = (refl⟩∘⟨ cap≈cap′ ⟩⊗⟨refl ⟩∘⟨refl) ⟩∘⟨refl

  -- Precomposition slides into the cap: `g` enters along the spectator wire, walks
  -- left past the cup and the associator, and is absorbed by `cap`.
  transposeˡ-natural : {cap : Z ⊗₀ X ⇒ unit} {cup : unit ⇒ X ⊗₀ W} {g : Y ⇒ Z} →
    transposeˡ cap cup ∘ g ≈ transposeˡ (cap ∘ (g ⊗₁ id)) cup
  transposeˡ-natural {cap = cap} {cup} {g} = begin
    transposeˡ cap cup ∘ g                                  ≈⟨ assoc ⟩
    cap-bendˡ cap ∘ cup-openʳ cup ∘ g                       ≈⟨ refl⟩∘⟨ assoc ⟩
    cap-bendˡ cap ∘ (id ⊗₁ cup) ∘ ρ⇐ ∘ g                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorʳ-commute-to ⟩
    cap-bendˡ cap ∘ (id ⊗₁ cup) ∘ (g ⊗₁ id) ∘ ρ⇐            ≈⟨ refl⟩∘⟨ pullˡ (⟺ whisker-comm) ⟩
    cap-bendˡ cap ∘ ((g ⊗₁ id) ∘ (id ⊗₁ cup)) ∘ ρ⇐          ≈⟨ refl⟩∘⟨ assoc ⟩
    cap-bendˡ cap ∘ (g ⊗₁ id) ∘ (id ⊗₁ cup) ∘ ρ⇐            ≈⟨ assoc²βε ⟩
    λ⇒ ∘ (cap ⊗₁ id) ∘ α⇐ ∘ (g ⊗₁ id) ∘ (id ⊗₁ cup) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ α⇐-⊗id-commute ⟩
    λ⇒ ∘ (cap ⊗₁ id) ∘ (((g ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ cup) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ pull-first merge₁ˡ ⟩
    λ⇒ ∘ (((cap ∘ (g ⊗₁ id)) ⊗₁ id) ∘ α⇐ ∘ cup-openʳ cup)   ≈˘⟨ assoc²βε ⟩
    transposeˡ (cap ∘ (g ⊗₁ id)) cup                        ∎

-- The two transposes compose into a single one: `capᵀ cap` slides into `cupᵀ`'s
-- counit (`capᵀ-ε`), leaving `cap` where `ε` was.
cupᵀ-capᵀ : {cup : unit ⇒ X ⊗₀ Z} {cap : Z ⊗₀ X ⇒ unit} →
  cupᵀ cup ∘ capᵀ cap ≈ λ⇒ ∘ (cap ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ cup) ∘ ρ⇐
cupᵀ-capᵀ {cup = cup} {cap} = begin
  transposeˡ ε cup ∘ capᵀ cap               ≈⟨ transposeˡ-natural ⟩
  transposeˡ (ε ∘ (capᵀ cap ⊗₁ id)) cup     ≈⟨ transposeˡ-resp-cap (capᵀ-ε cap) ⟩
  transposeˡ cap cup                        ≈⟨ assoc²βε ⟩
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

  private
    -- `capᵀ cap ∘ cupᵀ cup` acts trivially on the cup `η`, so it is the identity.
    cupᵀ-capᵀ-η : (id {D} ⊗₁ (capᵀ cap ∘ cupᵀ cup)) ∘ η {D} ≈ η
    cupᵀ-capᵀ-η = begin
      (id ⊗₁ (capᵀ cap ∘ cupᵀ cup)) ∘ η          ≈⟨ split₂ˡ ⟩∘⟨refl ⟩
      ((id ⊗₁ capᵀ cap) ∘ (id ⊗₁ cupᵀ cup)) ∘ η  ≈⟨ assoc ⟩
      (id ⊗₁ capᵀ cap) ∘ (id ⊗₁ cupᵀ cup) ∘ η    ≈⟨ refl⟩∘⟨ cupᵀ-η cup ⟩
      (id ⊗₁ capᵀ cap) ∘ cup                     ≈⟨ capᵀ-cup snakeᴰ ⟩
      η                                          ∎

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
        from-to = begin
          capᵀ cap ∘ cupᵀ cup                       ≈˘⟨ cupᵀ-unbend ⟩
          cupᵀ ((id ⊗₁ (capᵀ cap ∘ cupᵀ cup)) ∘ η)  ≈⟨ cupᵀ-resp-≈ cupᵀ-capᵀ-η ⟩
          cupᵀ η                                    ≈˘⟨ cupᵀ-resp-≈ (elimˡ ⊗.identity) ⟩
          cupᵀ ((id ⊗₁ id) ∘ η)                     ≈⟨ cupᵀ-unbend ⟩
          id                                        ∎
