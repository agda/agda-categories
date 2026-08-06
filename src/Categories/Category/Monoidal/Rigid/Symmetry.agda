{-# OPTIONS --without-K --safe #-}

-- Consequences of a symmetric monoidal structure for rigid monoidal categories:
-- * A left rigid structure induces a right rigid structure, and vice versa.
--   (This makes any symmetric rigid monoidal category a compact closed category.)
-- * The induced left and right dual morphisms agree.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Category.Monoidal.Rigid.Symmetry
    {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) (S : Symmetric M) where

open import Categories.Category.Monoidal.Rigid using (LeftRigid; RightRigid)

open Category C
open Monoidal M
open Symmetric S using (braided; commutative)
import Categories.Category.Monoidal.Utilities M as MonUtil
open import Categories.Category.Monoidal.Braided.Properties braided
  renaming (module Shorthands to BraidShorthands)
import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
import Categories.Category.Monoidal.Construction.Reverse as Reverse
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.CupCap M
  using (cup-bendˡ; cup-bendˡ-resp; cup-bendˡ-⊗; cup-openˡ; cup-openʳ)
open import Categories.Category.Monoidal.Symmetric.Properties S
  using (braiding-selfInverse; cup-swap; mirrorˡ)
open import Categories.Morphism.Reasoning C

open MonUtil.Shorthands
open BraidShorthands

private
  module RevProps = BraidedProperties (Reverse.Reverse-Braided braided)

  variable
    A B X Y Z : Obj

  abstract
    mirror-assoc : (id {X} ⊗₁ σ⇒ {Z} {Y})
                    ∘ σ⇐ {X} {Z ⊗₀ Y} ∘ α⇐
                    ∘ σ⇐ {Z} {Y ⊗₀ X} ∘ (σ⇒ ⊗₁ id)
                    ≈ α⇒
    mirror-assoc = begin
      id ⊗₁ σ⇒ ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ σ⇒ ⊗₁ id    ≈⟨ extendʳ mirrorˡ ⟩
      σ⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ σ⇐ ∘ σ⇒ ⊗₁ id    ≈⟨ reassoc-tail₅ ⟩
      (σ⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ σ⇐) ∘ σ⇒ ⊗₁ id  ≈⟨ refl⟩∘⟨ braiding-selfInverse ⟩⊗⟨refl ⟨
      (σ⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ σ⇐) ∘ σ⇐ ⊗₁ id  ≈⟨ reassoc-tail₅ ⟨
      σ⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ σ⇐ ∘ σ⇐ ⊗₁ id    ≈⟨ RevProps.assoc-reverse ⟩
      α⇒                                    ∎

  module Transpose {A B Y} {ε : A ⊗₀ Y ⇒ unit} {η : unit ⇒ Y ⊗₀ B} where
    abstract
      ε-split : id {B} ⊗₁ ε ≈ (id ⊗₁ (ε ∘ σ⇒)) ∘ (id ⊗₁ σ⇒)
      ε-split = begin
        id ⊗₁ ε                     ≈⟨ refl⟩⊗⟨ introʳ commutative ⟩
        id ⊗₁ (ε ∘ (σ⇒ ∘ σ⇒))       ≈⟨ refl⟩⊗⟨ sym-assoc ⟩
        id ⊗₁ ((ε ∘ σ⇒) ∘ σ⇒)       ≈⟨ split₂ˡ ⟩
        id ⊗₁ (ε ∘ σ⇒) ∘ id ⊗₁ σ⇒   ∎

      η-split : η ⊗₁ id {A} ≈ (σ⇒ ⊗₁ id) ∘ ((σ⇒ ∘ η) ⊗₁ id)
      η-split = begin
        η ⊗₁ id                     ≈⟨ introˡ commutative ⟩⊗⟨refl ⟩
        ((σ⇒ ∘ σ⇒) ∘ η) ⊗₁ id       ≈⟨ assoc ⟩⊗⟨refl ⟩
        (σ⇒ ∘ (σ⇒ ∘ η)) ⊗₁ id       ≈⟨ split₁ˡ ⟩
        σ⇒ ⊗₁ id ∘ (σ⇒ ∘ η) ⊗₁ id   ∎

    η′ : unit ⊗₀ A ⇒ (B ⊗₀ Y) ⊗₀ A
    η′ = (σ⇒ ∘ η) ⊗₁ id

    abstract
      braid-cup : (id ⊗₁ σ⇒) ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ (η ⊗₁ id) ≈ α⇒ ∘ η′
      braid-cup = begin
        id ⊗₁ σ⇒ ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ η ⊗₁ id           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ η-split ⟩
        id ⊗₁ σ⇒ ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ σ⇒ ⊗₁ id ∘ η′     ≈⟨ reassoc-tail₆ ○ mirror-assoc ⟩∘⟨refl ⟩
        α⇒ ∘ η′                                     ∎

      middle : (id ⊗₁ ε) ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ (η ⊗₁ id)
              ≈ (id ⊗₁ (ε ∘ σ⇒)) ∘ α⇒ ∘ ((σ⇒ ∘ η) ⊗₁ id)
      middle = begin
        id ⊗₁ ε ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ η ⊗₁ id                      ≈⟨ pushˡ ε-split ⟩
        id ⊗₁ (ε ∘ σ⇒) ∘ id ⊗₁ σ⇒ ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ η ⊗₁ id    ≈⟨ refl⟩∘⟨ braid-cup ⟩
        id ⊗₁ (ε ∘ σ⇒) ∘ α⇒ ∘ η′                              ∎

      middle-slide : (id ⊗₁ ε) ∘ σ⇐ ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐
                    ≈ (id ⊗₁ (ε ∘ σ⇒)) ∘ cup-bendˡ (σ⇒ ∘ η)
      middle-slide = begin
        id ⊗₁ ε ∘ σ⇐ ∘ α⇐ ∘ id ⊗₁ η ∘ ρ⇐                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cup-swap ⟩
        id ⊗₁ ε ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ cup-openˡ η            ≈⟨ reassoc-tail₆ ⟩
        (id ⊗₁ ε ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ η ⊗₁ id) ∘ λ⇐         ≈⟨ middle ⟩∘⟨refl ○ assoc²βε ⟩
        id ⊗₁ (ε ∘ σ⇒) ∘ cup-bendˡ (σ⇒ ∘ η)             ∎

abstract
  transposeˡ⇒ʳ : {ε : A ⊗₀ Y ⇒ unit} {η : unit ⇒ Y ⊗₀ B} →
    λ⇒ ∘ (ε ⊗₁ id) ∘ α⇐ ∘ cup-openʳ η
    ≈ ρ⇒ ∘ (id ⊗₁ (ε ∘ σ⇒)) ∘ cup-bendˡ (σ⇒ ∘ η)
  transposeˡ⇒ʳ {ε = ε} {η = η} = let open Transpose {ε = ε} {η = η} in begin
    λ⇒ ∘ ε ⊗₁ id ∘ α⇐ ∘ id ⊗₁ η ∘ ρ⇐            ≈⟨ pushˡ (⟺ inv-braiding-coherence) ⟩
    ρ⇒ ∘ σ⇐ ∘ ε ⊗₁ id ∘ α⇐ ∘ id ⊗₁ η ∘ ρ⇐       ≈⟨ refl⟩∘⟨ extendʳ σ⇐-comm ⟩
    ρ⇒ ∘ id ⊗₁ ε ∘ σ⇐ ∘ α⇐ ∘ id ⊗₁ η ∘ ρ⇐       ≈⟨ refl⟩∘⟨ middle-slide ⟩
    ρ⇒ ∘ id ⊗₁ (ε ∘ σ⇒) ∘ cup-bendˡ (σ⇒ ∘ η)    ∎

  transposeʳ⇒ˡ : {ε : A ⊗₀ Y ⇒ unit} {η : unit ⇒ Y ⊗₀ B} →
    ρ⇒ ∘ (id ⊗₁ (ε ∘ σ⇒)) ∘ cup-bendˡ (σ⇒ ∘ η)
    ≈ λ⇒ ∘ (ε ⊗₁ id) ∘ α⇐ ∘ cup-openʳ η
  transposeʳ⇒ˡ = ⟺ transposeˡ⇒ʳ

  braid-snakeˡ : {ηₗ : unit ⇒ X ⊗₀ Y} {εₗ : Y ⊗₀ X ⇒ unit} →
    ρ⇒ ∘ (id ⊗₁ εₗ)             ∘ cup-bendˡ ηₗ        ≈ id →
    λ⇒ ∘ ((εₗ ∘ σ⇒) ⊗₁ id) ∘ α⇐ ∘ cup-openʳ (σ⇒ ∘ ηₗ) ≈ id
  braid-snakeˡ {ηₗ = ηₗ} {εₗ} snake = begin
    λ⇒ ∘ (εₗ ∘ σ⇒) ⊗₁ id ∘ α⇐ ∘ cup-openʳ (σ⇒ ∘ ηₗ)           ≈⟨ transposeˡ⇒ʳ ⟩
    ρ⇒ ∘ id ⊗₁ ((εₗ ∘ σ⇒) ∘ σ⇒) ∘ cup-bendˡ (σ⇒ ∘ (σ⇒ ∘ ηₗ))
      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ cancelʳ commutative ⟩∘⟨refl ⟩
    ρ⇒ ∘ id ⊗₁ εₗ ∘ cup-bendˡ (σ⇒ ∘ (σ⇒ ∘ ηₗ))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cup-bendˡ-resp (cancelˡ commutative) ⟩
    ρ⇒ ∘ id ⊗₁ εₗ ∘ cup-bendˡ ηₗ                              ≈⟨ snake ⟩
    id                                                        ∎

  braid-snakeʳ : {ηᵣ : unit ⇒ Y ⊗₀ X} {εᵣ : X ⊗₀ Y ⇒ unit} →
    λ⇒ ∘ (εᵣ ⊗₁ id) ∘ α⇐   ∘ cup-openʳ ηᵣ         ≈ id →
    ρ⇒ ∘ (id ⊗₁ (εᵣ ∘ σ⇒)) ∘ cup-bendˡ (σ⇒ ∘ ηᵣ)  ≈ id
  braid-snakeʳ {ηᵣ = ηᵣ} {εᵣ = εᵣ} snake = transposeʳ⇒ˡ ○ snake

left⇒right : LeftRigid M → RightRigid M
left⇒right L = record
  { _⁻¹ = _⁻¹
  ; η = σ⇒ ∘ η
  ; ε = ε ∘ σ⇒
  ; snake₁ = braid-snakeˡ snake₁
  ; snake₂ = braid-snakeʳ snake₂
  }
  where open LeftRigid L using (_⁻¹; η; ε; snake₁; snake₂)

right⇒left : RightRigid M → LeftRigid M
right⇒left R = record
  { _⁻¹ = _⁻¹
  ; η = σ⇒ ∘ η
  ; ε = ε ∘ σ⇒
  ; snake₁ = braid-snakeʳ snake₁
  ; snake₂ = braid-snakeˡ snake₂
  }
  where open RightRigid R using (_⁻¹; η; ε; snake₁; snake₂)

-- Both round-trips just cancel a braiding against its inverse.
η-roundtripˡ : (L : LeftRigid M) →
  LeftRigid.η (right⇒left (left⇒right L)) {X} ≈ LeftRigid.η L
η-roundtripˡ L = cancelˡ commutative

ε-roundtripˡ : (L : LeftRigid M) →
  LeftRigid.ε (right⇒left (left⇒right L)) {X} ≈ LeftRigid.ε L
ε-roundtripˡ L = cancelʳ commutative

η-roundtripʳ : (R : RightRigid M) →
  RightRigid.η (left⇒right (right⇒left R)) {X} ≈ RightRigid.η R
η-roundtripʳ R = cancelˡ commutative

ε-roundtripʳ : (R : RightRigid M) →
  RightRigid.ε (left⇒right (right⇒left R)) {X} ≈ RightRigid.ε R
ε-roundtripʳ R = cancelʳ commutative

abstract
  dual₁ˡ≈dual₁ʳ : (L : LeftRigid M) → (f : X ⇒ Y) →
    LeftRigid.dual₁ L f ≈ RightRigid.dual₁ (left⇒right L) f
  dual₁ˡ≈dual₁ʳ L f = begin
    dual₁ f                                                 ≈⟨ transposeˡ⇒ʳ ⟩
    ρ⇒ ∘ (id ⊗₁ (ε ∘ σ⇒)) ∘ cup-bendˡ (σ⇒ ∘ (f ⊗₁ id ∘ η))  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cup-bend-eq ⟩
    ρ⇒ ∘ (id ⊗₁ (ε ∘ σ⇒)) ∘ (id ⊗₁ f ⊗₁ id) ∘ cup-bendˡ ηʳ  ∎
    where
      open LeftRigid L using (_⁻¹; η; ε; dual₁)

      ηʳ : unit ⇒ X ⁻¹ ⊗₀ X
      ηʳ = σ⇒ ∘ η

      cup-bend-eq : cup-bendˡ {A = Y ⁻¹} (σ⇒ ∘ (f ⊗₁ id ∘ η))
                    ≈ (id ⊗₁ f ⊗₁ id) ∘ cup-bendˡ ηʳ
      cup-bend-eq = cup-bendˡ-resp (extendʳ σ⇒-comm) ○ ⟺ (cup-bendˡ-⊗ ηʳ)

  dual₁-roundtripʳ : (R : RightRigid M) → (f : X ⇒ Y) →
    RightRigid.dual₁ (left⇒right (right⇒left R)) f ≈ RightRigid.dual₁ R f
  dual₁-roundtripʳ R f = begin
    RightRigid.dual₁ (left⇒right (right⇒left R)) f
      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ ε-roundtripʳ R ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id ⊗₁ RightRigid.ε R) ∘ (id ⊗₁ (f ⊗₁ id))
      ∘ cup-bendˡ (RightRigid.η (left⇒right (right⇒left R)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cup-bendˡ-resp (η-roundtripʳ R) ⟩
    RightRigid.dual₁ R f ∎

  dual₁-roundtripˡ : (L : LeftRigid M) → (f : X ⇒ Y) →
    LeftRigid.dual₁ (right⇒left (left⇒right L)) f ≈ LeftRigid.dual₁ L f
  dual₁-roundtripˡ L f = let R[L] = left⇒right L in begin
    LeftRigid.dual₁ (right⇒left R[L]) f                 ≈⟨ dual₁ˡ≈dual₁ʳ (right⇒left R[L]) f ⟩
    RightRigid.dual₁ (left⇒right (right⇒left R[L])) f   ≈⟨ dual₁-roundtripʳ R[L] f ⟩
    RightRigid.dual₁ R[L] f                             ≈⟨ dual₁ˡ≈dual₁ʳ L f ⟨
    LeftRigid.dual₁ L f ∎

  dual₁ʳ≈dual₁ˡ : (R : RightRigid M) → (f : X ⇒ Y) →
    RightRigid.dual₁ R f ≈ LeftRigid.dual₁ (right⇒left R) f
  dual₁ʳ≈dual₁ˡ R f = begin
    RightRigid.dual₁ R f                            ≈⟨ dual₁-roundtripʳ R f ⟨
    RightRigid.dual₁ (left⇒right (right⇒left R)) f  ≈⟨ dual₁ˡ≈dual₁ʳ (right⇒left R) f ⟨
    LeftRigid.dual₁ (right⇒left R) f                ∎
