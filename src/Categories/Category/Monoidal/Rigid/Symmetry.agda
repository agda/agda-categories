{-# OPTIONS --without-K --safe #-}

-- Consequences of a symmetric monoidal structure for rigid monoidal categories:
-- * A left rigid structure induces a right rigid structure, and vice versa.
--   (This makes any symmetric rigid monoidal category a compact closed category.)
-- * The left and right duals of an object are isomorphic, and the isomorphism is natural.
-- * The dual of the dual of an object is canonically isomorphic to the original object

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Category.Monoidal.Rigid.Symmetry
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C) (S : Symmetric M) where

open import Categories.Category.Monoidal.Rigid using (LeftRigid; RightRigid)

open Category C
open Monoidal M
open Symmetric S using (braided; commutative)
import Categories.Category.Monoidal.Utilities M as MonUtil
open import Categories.Category.Monoidal.Braided.Properties braided
  renaming (module Shorthands to BraidShorthands)
import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
import Categories.Category.Monoidal.Construction.Reverse as Reverse
import Categories.Category.Monoidal.Interchange.Symmetric as SymmetricInterchange
import Categories.Category.Monoidal.Rigid.Dual as RigidDual
import Categories.Category.Monoidal.Rigid.Properties as RigidPropertiesModule
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Properties M using (coherence-inv₃)
open import Categories.Category.Monoidal.Reassociation M
  using (α⇐-id⊗-commute; whisker-comm)
open import Categories.Category.Monoidal.CupCap M
  using (cup-openʳ; parallel-cups-commute)
open import Categories.Category.Monoidal.Symmetric.Properties S
  using (braiding-selfInverse; cup-swap; middle-braid; mirrorˡ)
open import Categories.Morphism.Reasoning C
open import Categories.Morphism C using (_≅_; module ≅)

open MonUtil.Shorthands
open BraidShorthands

private
  module Interchange = SymmetricInterchange S
  module RevProps = BraidedProperties (Reverse.Reverse-Braided braided)

  variable
    A B X Y Z : Obj

  i⇒ : (A ⊗₀ B) ⊗₀ (X ⊗₀ Y) ⇒ (A ⊗₀ X) ⊗₀ (B ⊗₀ Y)
  i⇒ = _≅_.from Interchange.swapInner-iso

  mirror-assoc : (id {X} ⊗₁ σ⇒ {Z} {Y})
                  ∘ σ⇐ {X} {Z ⊗₀ Y} ∘ α⇐
                  ∘ σ⇐ {Z} {Y ⊗₀ X} ∘ (σ⇒ ⊗₁ id)
                  ≈ α⇒
  mirror-assoc = begin
    id ⊗₁ σ⇒ ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ σ⇒ ⊗₁ id  ≈⟨ extendʳ mirrorˡ ⟩
    σ⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ σ⇐ ∘ σ⇒ ⊗₁ id
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ braiding-selfInverse ⟩⊗⟨refl ⟩
    σ⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ σ⇐ ∘ σ⇐ ⊗₁ id
      ≈⟨ RevProps.assoc-reverse ⟩
    α⇒ ∎

  module Transpose
      {A B Y} {ε : A ⊗₀ Y ⇒ unit} {η : unit ⇒ Y ⊗₀ B} where

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

    -- Reassociate the braided snake so its core matches `mirror-assoc`.
    braid-tail :
      (id ⊗₁ σ⇒) ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ (σ⇒ ⊗₁ id) ∘ η′
      ≈ α⇒ ∘ η′
    braid-tail = begin
      id ⊗₁ σ⇒ ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ σ⇒ ⊗₁ id ∘ η′     ≈⟨ reassoc-tail₆ ⟩
      (id ⊗₁ σ⇒ ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ σ⇒ ⊗₁ id) ∘ η′   ≈⟨ mirror-assoc ⟩∘⟨refl ⟩
      α⇒ ∘ η′                                     ∎

    middle : (id ⊗₁ ε) ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ (η ⊗₁ id)
             ≈ (id ⊗₁ (ε ∘ σ⇒)) ∘ α⇒ ∘ ((σ⇒ ∘ η) ⊗₁ id)
    middle = begin
      id ⊗₁ ε ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ η ⊗₁ id
        ≈⟨ pushˡ ε-split ⟩
      id ⊗₁ (ε ∘ σ⇒) ∘ id ⊗₁ σ⇒ ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ η ⊗₁ id
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ η-split ⟩
      id ⊗₁ (ε ∘ σ⇒) ∘ id ⊗₁ σ⇒ ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ σ⇒ ⊗₁ id ∘ η′
        ≈⟨ refl⟩∘⟨ braid-tail ⟩
      id ⊗₁ (ε ∘ σ⇒) ∘ α⇒ ∘ η′ ∎

    middle-slide :
      (id ⊗₁ ε) ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ (η ⊗₁ id) ∘ λ⇐
      ≈ (id ⊗₁ (ε ∘ σ⇒)) ∘ α⇒ ∘ ((σ⇒ ∘ η) ⊗₁ id) ∘ λ⇐
    middle-slide = begin
      id ⊗₁ ε ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ η ⊗₁ id ∘ λ⇐         ≈⟨ reassoc-tail₆ ⟩
      (id ⊗₁ ε ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ η ⊗₁ id) ∘ λ⇐       ≈⟨ middle ⟩∘⟨refl ⟩
      (id ⊗₁ (ε ∘ σ⇒) ∘ α⇒ ∘ (σ⇒ ∘ η) ⊗₁ id) ∘ λ⇐   ≈⟨ assoc²βε ⟩
      id ⊗₁ (ε ∘ σ⇒) ∘ α⇒ ∘ (σ⇒ ∘ η) ⊗₁ id ∘ λ⇐     ∎

transposeˡ⇒ʳ : {ε : A ⊗₀ Y ⇒ unit} {η : unit ⇒ Y ⊗₀ B} →
  λ⇒ ∘ (ε ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐
  ≈ ρ⇒ ∘ (id ⊗₁ (ε ∘ σ⇒)) ∘ α⇒ ∘ ((σ⇒ ∘ η) ⊗₁ id) ∘ λ⇐
transposeˡ⇒ʳ {ε = ε} {η = η} =
  let open Transpose {ε = ε} {η = η} in begin
  λ⇒ ∘ ε ⊗₁ id ∘ α⇐ ∘ id ⊗₁ η ∘ ρ⇐  ≈⟨ pushˡ (⟺ inv-braiding-coherence) ⟩
  ρ⇒ ∘ σ⇐ ∘ ε ⊗₁ id ∘ α⇐ ∘ id ⊗₁ η ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ extendʳ σ⇐-comm ⟩
  ρ⇒ ∘ id ⊗₁ ε ∘ σ⇐ ∘ α⇐ ∘ id ⊗₁ η ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cup-swap ⟩
  ρ⇒ ∘ id ⊗₁ ε ∘ σ⇐ ∘ α⇐ ∘ σ⇐ ∘ η ⊗₁ id ∘ λ⇐
    ≈⟨ refl⟩∘⟨ middle-slide ⟩
  ρ⇒ ∘ id ⊗₁ (ε ∘ σ⇒) ∘ α⇒ ∘ (σ⇒ ∘ η) ⊗₁ id ∘ λ⇐ ∎

transposeʳ⇒ˡ : {ε : A ⊗₀ Y ⇒ unit} {η : unit ⇒ Y ⊗₀ B} →
  ρ⇒ ∘ (id ⊗₁ (ε ∘ σ⇒)) ∘ α⇒ ∘ ((σ⇒ ∘ η) ⊗₁ id) ∘ λ⇐
  ≈ λ⇒ ∘ (ε ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐
transposeʳ⇒ˡ = ⟺ transposeˡ⇒ʳ

braid-snakeˡ : {ηₗ : unit ⇒ X ⊗₀ Y} {εₗ : Y ⊗₀ X ⇒ unit} →
  ρ⇒ ∘ (id ⊗₁ εₗ) ∘ α⇒ ∘ (ηₗ ⊗₁ id) ∘ λ⇐                    ≈ id →
  λ⇒ ∘ ((εₗ ∘ σ⇒) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ (σ⇒ ∘ ηₗ)) ∘ ρ⇐  ≈ id
braid-snakeˡ {ηₗ = ηₗ} {εₗ} snake = begin
  λ⇒ ∘ (εₗ ∘ σ⇒) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ∘ ηₗ) ∘ ρ⇐
    ≈⟨ transposeˡ⇒ʳ ⟩
  ρ⇒ ∘ id ⊗₁ ((εₗ ∘ σ⇒) ∘ σ⇒) ∘ α⇒ ∘ (σ⇒ ∘ (σ⇒ ∘ ηₗ)) ⊗₁ id ∘ λ⇐
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ cancelʳ commutative ⟩∘⟨refl ⟩
  ρ⇒ ∘ id ⊗₁ εₗ ∘ α⇒ ∘ (σ⇒ ∘ (σ⇒ ∘ ηₗ)) ⊗₁ id ∘ λ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ commutative ⟩⊗⟨refl ⟩∘⟨refl ⟩
  ρ⇒ ∘ id ⊗₁ εₗ ∘ α⇒ ∘ ηₗ ⊗₁ id ∘ λ⇐
    ≈⟨ snake ⟩
  id ∎

braid-snakeʳ : {ηᵣ : unit ⇒ Y ⊗₀ X} {εᵣ : X ⊗₀ Y ⇒ unit} →
  λ⇒ ∘ (εᵣ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ ηᵣ) ∘ ρ⇐                ≈ id →
  ρ⇒ ∘ (id ⊗₁ (εᵣ ∘ σ⇒)) ∘ α⇒ ∘ ((σ⇒ ∘ ηᵣ) ⊗₁ id) ∘ λ⇐  ≈ id
braid-snakeʳ {ηᵣ = ηᵣ} {εᵣ = εᵣ} snake = begin
  ρ⇒ ∘ id ⊗₁ (εᵣ ∘ σ⇒) ∘ α⇒ ∘ (σ⇒ ∘ ηᵣ) ⊗₁ id ∘ λ⇐  ≈⟨ transposeʳ⇒ˡ ⟩
  λ⇒ ∘ εᵣ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ ηᵣ ∘ ρ⇐                ≈⟨ snake ⟩
  id                                                ∎

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

dual₁ˡ≈dual₁ʳ : (L : LeftRigid M) → (f : X ⇒ Y) →
  LeftRigid.dual₁ L f ≈ RightRigid.dual₁ (left⇒right L) f
dual₁ˡ≈dual₁ʳ L f = begin
  dual₁ f                                                       ≈⟨ transposeˡ⇒ʳ ⟩
  ρ⇒ ∘ (id ⊗₁ (ε ∘ σ⇒)) ∘ α⇒ ∘ (σ⇒ ∘ (f ⊗₁ id ∘ η)) ⊗₁ id ∘ λ⇐  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ f-slide-α ⟩
  ρ⇒ ∘ (id ⊗₁ (ε ∘ σ⇒)) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ α⇒ ∘ (σ⇒ ∘ η) ⊗₁ id ∘ λ⇐
  ∎
  where
    open LeftRigid L using (_⁻¹; η; ε; dual₁)

    ηʳ : unit ⇒ X ⁻¹ ⊗₀ X
    ηʳ = σ⇒ ∘ η

    f-slide : σ⇒ ∘ ((f ⊗₁ id) ∘ η) ≈ id ⊗₁ f ∘ ηʳ
    f-slide = extendʳ σ⇒-comm

    f-slide-α :
      α⇒ ∘ ((σ⇒ ∘ ((f ⊗₁ id) ∘ η)) ⊗₁ id) ∘ λ⇐
      ≈ (id ⊗₁ (f ⊗₁ id)) ∘ α⇒ ∘ (ηʳ ⊗₁ id) ∘ λ⇐
    f-slide-α = begin
      α⇒ ∘ (σ⇒ ∘ (f ⊗₁ id ∘ η)) ⊗₁ id ∘ λ⇐      ≈⟨ refl⟩∘⟨ f-slide ⟩⊗⟨refl ⟩∘⟨refl ⟩
      α⇒ ∘ (id ⊗₁ f ∘ ηʳ) ⊗₁ id ∘ λ⇐            ≈⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
      α⇒ ∘ ((id ⊗₁ f) ⊗₁ id ∘ ηʳ ⊗₁ id) ∘ λ⇐    ≈⟨ refl⟩∘⟨ assoc ⟩
      α⇒ ∘ (id ⊗₁ f) ⊗₁ id ∘ ηʳ ⊗₁ id ∘ λ⇐      ≈⟨ extendʳ assoc-commute-from ⟩
      id ⊗₁ (f ⊗₁ id) ∘ α⇒ ∘ ηʳ ⊗₁ id ∘ λ⇐      ∎

dual₁-roundtripʳ : (R : RightRigid M) → (f : X ⇒ Y) →
  RightRigid.dual₁ (left⇒right (right⇒left R)) f ≈ RightRigid.dual₁ R f
dual₁-roundtripʳ R f = begin
  RightRigid.dual₁ (left⇒right (right⇒left R)) f
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ ε-roundtripʳ R ⟩∘⟨refl ⟩
  ρ⇒ ∘ (id ⊗₁ RightRigid.ε R) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ α⇒
    ∘ (RightRigid.η (left⇒right (right⇒left R)) ⊗₁ id) ∘ λ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ η-roundtripʳ R ⟩⊗⟨refl ⟩∘⟨refl ⟩
  RightRigid.dual₁ R f ∎

dual₁-roundtripˡ : (L : LeftRigid M) → (f : X ⇒ Y) →
  LeftRigid.dual₁ (right⇒left (left⇒right L)) f ≈ LeftRigid.dual₁ L f
dual₁-roundtripˡ L f = begin
  LeftRigid.dual₁ (right⇒left (left⇒right L)) f
    ≈⟨ dual₁ˡ≈dual₁ʳ (right⇒left (left⇒right L)) f ⟩
  RightRigid.dual₁ (left⇒right (right⇒left (left⇒right L))) f
    ≈⟨ dual₁-roundtripʳ (left⇒right L) f ⟩
  RightRigid.dual₁ (left⇒right L) f
    ≈˘⟨ dual₁ˡ≈dual₁ʳ L f ⟩
  LeftRigid.dual₁ L f
    ∎

dual₁ʳ≈dual₁ˡ : (R : RightRigid M) → (f : X ⇒ Y) →
  RightRigid.dual₁ R f ≈ LeftRigid.dual₁ (right⇒left R) f
dual₁ʳ≈dual₁ˡ R f = begin
  RightRigid.dual₁ R f                            ≈˘⟨ dual₁-roundtripʳ R f ⟩
  RightRigid.dual₁ (left⇒right (right⇒left R)) f  ≈˘⟨ dual₁ˡ≈dual₁ʳ (right⇒left R) f ⟩
  LeftRigid.dual₁ (right⇒left R) f                ∎

-- The Drinfeld double-dual isomorphism `(X ⁻¹) ⁻¹ ≅ X`.  It holds in any braided
-- rigid category, but the strict-left-dual route below picks up the ribbon twist
-- `σ⇒ ∘ σ⇒`, which vanishes only under symmetry — so we prove just that case.
--
-- `η`/`ε` make `X ⁻¹` a left dual of `X`; braiding them makes `X` a *left* dual of
-- `X ⁻¹` (the bends are the same, read with the two wires crossed), and uniqueness
-- of left duals then identifies `X` with `(X ⁻¹) ⁻¹`.
--
--   X ⁻¹        X                X          X ⁻¹
--     │         │                 ╲        ╱
--     │         │                  ╲      ╱          σ⇒ ∘ η : the same bend,
--     ╰─────────╯   ← η             ╲────╱           with the wires crossed
--
-- The twist is where a merely braided category would differ: undoing the crossing
-- on the other side costs a second `σ⇒`, and `σ⇒ ∘ σ⇒ ≈ id` is exactly symmetry.

-- The braiding recasts `X` (a right dual of `X ⁻¹`) as a left dual of `X ⁻¹`;
-- uniqueness of left duals identifies it with `(X ⁻¹) ⁻¹`.
module DoubleDualˡ (L : LeftRigid M) where
  open LeftRigid L using (_⁻¹; η; ε; snake₁; snake₂; dual₁)
  open import Categories.Category.Monoidal.Rigid.Dual M L
    using (cupˡ; cupᵀ-η; cupᵀ-unique; dual-uniqueˡ; dual₁-cup)
  module RigidProperties = RigidPropertiesModule M
  open RigidProperties.Left L using (⊗-cup; ⁻¹-flip-⊗⁻¹)

  private
    ⊗-cup-interchange :
      i⇒ {X} {X ⁻¹} {Y} {Y ⁻¹} ∘ (η ⊗₁ η) ∘ λ⇐ ≈ (id ⊗₁ σ⇒) ∘ ⊗-cup
    ⊗-cup-interchange {X} {Y} = begin
      (α⇐ ∘ (id ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒) ∘ ((η ⊗₁ η) ∘ λ⇐)
        ≈⟨ assoc²βε ⟩
      α⇐ ∘ (id ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒ ∘ (η ⊗₁ η) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
      α⇐ ∘ (id ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒
        ∘ (η ⊗₁ id) ∘ (id ⊗₁ η) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ unitorˡ-commute-to ⟩
      α⇐ ∘ (id ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒
        ∘ (η ⊗₁ id) ∘ λ⇐ ∘ η
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ parallel-cups-commute ⟩
      α⇐ ∘ (id ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐))
        ∘ (id ⊗₁ cup-openʳ η) ∘ η
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ ((α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ cup-openʳ η)) ∘ η
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ (refl⟩∘⟨ cup-swap)) ⟩∘⟨refl ⟩
      α⇐ ∘ (id ⊗₁ ((α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ σ⇐
        ∘ (η ⊗₁ id) ∘ λ⇐)) ∘ η
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ pullˡ middle-braid) ⟩∘⟨refl ⟩
      α⇐ ∘ (id ⊗₁ (((id ⊗₁ σ⇒) ∘ α⇒) ∘ ((η ⊗₁ id) ∘ λ⇐))) ∘ η
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ assoc) ⟩∘⟨refl ⟩
      α⇐ ∘ (id ⊗₁ ((id ⊗₁ σ⇒) ∘ cupˡ)) ∘ η
        ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ (id ⊗₁ σ⇒)) ∘ (id ⊗₁ cupˡ) ∘ η
        ≈˘⟨ extendʳ α⇐-id⊗-commute ⟩
      (id ⊗₁ σ⇒) ∘ α⇐ ∘ (id ⊗₁ cupˡ) ∘ η  ∎

    tensor-cup-braiding :
      (σ⇒ {X} {Y} ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ ⊗-cup {X} {Y}
      ≈ (id {Y ⊗₀ X} ⊗₁ σ⇒ {X ⁻¹} {Y ⁻¹}) ∘ ⊗-cup {Y} {X}
    tensor-cup-braiding {X} {Y} = begin
      (σ⇒ ⊗₁ id) ∘ ⊗-cup
        ≈⟨ intro-center (⊗-cancel identity² commutative) ⟩
      (σ⇒ ⊗₁ id) ∘ ((id ⊗₁ σ⇒ ∘ id ⊗₁ σ⇒) ∘ ⊗-cup)
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (σ⇒ ⊗₁ id) ∘ (id ⊗₁ σ⇒) ∘ (id ⊗₁ σ⇒) ∘ ⊗-cup
        ≈⟨ pullˡ (⟺ serialize₁₂) ⟩
      (σ⇒ ⊗₁ σ⇒) ∘ (id ⊗₁ σ⇒) ∘ ⊗-cup
        ≈˘⟨ refl⟩∘⟨ ⊗-cup-interchange ⟩
      (σ⇒ ⊗₁ σ⇒) ∘ i⇒ ∘ (η ⊗₁ η) ∘ λ⇐
        ≈⟨ extendʳ Interchange.swapInner-braiding′ ⟩
      i⇒ ∘ σ⇒ ∘ (η ⊗₁ η) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ extendʳ σ⇒-comm ⟩
      i⇒ ∘ (η ⊗₁ η) ∘ σ⇒ ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (⟺ braiding-selfInverse) ⟩∘⟨refl ⟩
      i⇒ ∘ (η ⊗₁ η) ∘ σ⇐ ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braiding-coherence-inv ⟩
      i⇒ ∘ (η ⊗₁ η) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ coherence-inv₃ ⟩
      i⇒ ∘ (η ⊗₁ η) ∘ λ⇐
        ≈⟨ ⊗-cup-interchange ⟩
      (id ⊗₁ σ⇒) ∘ ⊗-cup  ∎

  dual-braiding-compat : ⁻¹-flip-⊗⁻¹ {X} {Y} ∘ dual₁ σ⇒ ≈ σ⇒ ∘ ⁻¹-flip-⊗⁻¹
  dual-braiding-compat = cupᵀ-unique (begin
    (id ⊗₁ (⁻¹-flip-⊗⁻¹ ∘ dual₁ σ⇒)) ∘ η  ≈⟨ pushˡ split₂ˡ ⟩
    (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ (id ⊗₁ dual₁ σ⇒) ∘ η
      ≈⟨ refl⟩∘⟨ dual₁-cup ⟩
    (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ (σ⇒ ⊗₁ id) ∘ η
      ≈⟨ extendʳ (⟺ whisker-comm) ⟩
    (σ⇒ ⊗₁ id) ∘ (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ η
      ≈⟨ refl⟩∘⟨ cupᵀ-η ⊗-cup ⟩
    (σ⇒ ⊗₁ id) ∘ ⊗-cup                         ≈⟨ tensor-cup-braiding ⟩
    (id ⊗₁ σ⇒) ∘ ⊗-cup                         ≈˘⟨ refl⟩∘⟨ cupᵀ-η ⊗-cup ⟩
    (id ⊗₁ σ⇒) ∘ (id ⊗₁ ⁻¹-flip-⊗⁻¹) ∘ η     ≈⟨ pullˡ merge₂ˡ ⟩
    (id ⊗₁ (σ⇒ ∘ ⁻¹-flip-⊗⁻¹)) ∘ η           ∎)

  ⁻¹⁻¹≅ : (X ⁻¹) ⁻¹ ≅ X
  ⁻¹⁻¹≅ = ≅.sym (dual-uniqueˡ (σ⇒ ∘ η) (ε ∘ σ⇒)
                              (braid-snakeʳ snake₂) (braid-snakeˡ snake₁))

  j⇒ : (X ⁻¹) ⁻¹ ⇒ X
  j⇒ = _≅_.from ⁻¹⁻¹≅

  j⇐ : X ⇒ (X ⁻¹) ⁻¹
  j⇐ = _≅_.to ⁻¹⁻¹≅

  private
    j-cup : (id {X ⁻¹} ⊗₁ j⇒ {X}) ∘ η {X ⁻¹} ≈ σ⇒ ∘ η {X}
    j-cup = cupᵀ-η (σ⇒ ∘ η)

    double-dual-cup : (f : X ⇒ Y) →
      (id {X ⁻¹} ⊗₁ (j⇒ {Y} ∘ dual₁ (dual₁ f))) ∘ η {X ⁻¹}
      ≈ (id ⊗₁ (f ∘ j⇒)) ∘ η
    double-dual-cup f = begin
      (id ⊗₁ (j⇒ ∘ dual₁ (dual₁ f))) ∘ η            ≈⟨ pushˡ split₂ˡ ⟩
      (id ⊗₁ j⇒) ∘ (id ⊗₁ dual₁ (dual₁ f)) ∘ η      ≈⟨ refl⟩∘⟨ dual₁-cup ⟩
      (id ⊗₁ j⇒) ∘ (dual₁ f ⊗₁ id) ∘ η              ≈⟨ extendʳ (⟺ whisker-comm) ⟩
      (dual₁ f ⊗₁ id) ∘ (id ⊗₁ j⇒) ∘ η              ≈⟨ refl⟩∘⟨ j-cup ⟩
      (dual₁ f ⊗₁ id) ∘ σ⇒ ∘ η                      ≈⟨ extendʳ (⟺ σ⇒-comm) ⟩
      σ⇒ ∘ (id ⊗₁ dual₁ f) ∘ η                      ≈⟨ refl⟩∘⟨ dual₁-cup ⟩
      σ⇒ ∘ (f ⊗₁ id) ∘ η                            ≈⟨ extendʳ σ⇒-comm ⟩
      (id ⊗₁ f) ∘ σ⇒ ∘ η                            ≈˘⟨ refl⟩∘⟨ j-cup ⟩
      (id ⊗₁ f) ∘ (id ⊗₁ j⇒) ∘ η                    ≈⟨ pullˡ merge₂ˡ ⟩
      (id ⊗₁ (f ∘ j⇒)) ∘ η                          ∎

  double-dual-natural : (f : X ⇒ Y) →
    j⇒ {Y} ∘ dual₁ (dual₁ f) ≈ f ∘ j⇒ {X}
  double-dual-natural f = cupᵀ-unique (double-dual-cup f)

  double-dual-on-morphisms : (f : X ⇒ Y) →
    dual₁ (dual₁ f) ≈ j⇐ ∘ f ∘ j⇒
  double-dual-on-morphisms {Y = Y} f = switch-fromtoˡ (⁻¹⁻¹≅ {X = Y}) (double-dual-natural f)

module DoubleDualʳ (R : RightRigid M) where
  open RightRigid R using (_⁻¹; dual₁)
  open DoubleDualˡ (right⇒left R) public using (⁻¹⁻¹≅; j⇒; j⇐)

  private
    module L = LeftRigid (right⇒left R)
    module D = RigidDual M (right⇒left R)

  double-dual-on-morphisms : (f : X ⇒ Y) →
    dual₁ (dual₁ f)
    ≈ _≅_.to (⁻¹⁻¹≅ {X = Y}) ∘ f ∘ _≅_.from (⁻¹⁻¹≅ {X = X})
  double-dual-on-morphisms f = begin
    dual₁ (dual₁ f)        ≈⟨ dual₁ʳ≈dual₁ˡ R (dual₁ f) ⟩
    L.dual₁ (dual₁ f)      ≈⟨ D.dual₁-resp-≈ (dual₁ʳ≈dual₁ˡ R f) ⟩
    L.dual₁ (L.dual₁ f)    ≈⟨ DoubleDualˡ.double-dual-on-morphisms (right⇒left R) f ⟩
    _≅_.to ⁻¹⁻¹≅ ∘ f ∘ _≅_.from ⁻¹⁻¹≅  ∎
