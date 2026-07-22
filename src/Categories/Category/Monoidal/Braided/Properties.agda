{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Braided using (Braided)

module Categories.Category.Monoidal.Braided.Properties
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (BM : Braided M) where

open import Algebra.Bundles using (CommutativeMonoid; Monoid)
open import Data.Product using (_,_)

import Categories.Category.Construction.Core C as Core
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Scalars M using (Scalar; _·ʳ_; _·ˡ_)
import Categories.Category.Monoidal.Utilities M as MonoidalUtilities
open import Categories.Functor using (Functor)
open import Categories.Morphism.Reasoning C hiding (push-eq)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper; module ≃)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
  using (push-eq; flip-bifunctor-NI)

open Category C
open Commutation C
open Braided BM
open MonoidalUtilities using
  (_⊗ᵢ_; Obj-⊗-Monoid; unitorˡ-naturalIsomorphism; unitorʳ-naturalIsomorphism)
open MonoidalUtilities.Shorthands
open Core.Shorthands
open Commutationᵢ

private
  variable
    X Y Z : Obj

-- Shorthands for the braiding

module Shorthands where

  σ⇒ : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
  σ⇒ {X} {Y} = braiding.⇒.η (X , Y)

  σ⇐ : ∀ {X Y} → Y ⊗₀ X ⇒ X ⊗₀ Y
  σ⇐ {X} {Y} = braiding.⇐.η (X , Y)

  σ⇒-comm : ∀ {X Y Z W} {f : X ⇒ Y} {g : Z ⇒ W} →
            σ⇒ ∘ (f ⊗₁ g) ≈ (g ⊗₁ f) ∘ σ⇒
  σ⇒-comm {f = f} {g} = braiding.⇒.commute (f , g)

  σ⇐-comm : ∀ {X Y Z W} {f : X ⇒ Y} {g : Z ⇒ W} →
            σ⇐ ∘ (g ⊗₁ f) ≈ (f ⊗₁ g) ∘ σ⇐
  σ⇐-comm {f = f} {g} = braiding.⇐.commute (f , g)

  σ = braiding.FX≅GX

open Shorthands

private

  -- It's easier to prove the following lemma, which is the desired
  -- coherence theorem moduolo application of the |-⊗ unit| functor.
  -- Because |-⊗ unit| is equivalent to the identity functor, the
  -- lemma and the theorem are equivalent.

  -- The following diagram illustrates the hexagon that we are
  -- operating on. The main outer hexagon is hexagon₁, the braiding
  -- coherence, instantiated with X, 1 and 1 (Here we denote the unit
  -- by 1 for brevity).
  -- In the middle are X1 and 1X along with morphisms towards them.
  -- The lower hexagon (given by the double lines) commutes and is
  -- an intermediary in the final proof. It is there to effectively
  -- get rid of the top half of the main hexagon.
  -- The rest of the proof is isolating the bottom left triangle
  -- which represents our desired identity. It is doing that by
  -- proving that the pentagon to the right of it commutes.
  -- The pentagon commuting is, in turn, proved by gluing the
  -- rightmost "square" onto the middle triangle.
  --
  --
  --       ┌─────>  X(11)  ─────────>  (11)X ──────┐
  --      ┌┘ α        │        σ         │       α └┐
  --     ┌┘           │id⊗λ              │λ⊗id     └┐
  --    ┌┘            V                  V           V
  --  (X1)1 ═══════> X1  ════════════>  1X <══════ 1(1X)
  --    ╚╗   ρ⊗id     Λ <───┐  σ              λ      Λ
  --     ╚╗           │λ⊗id └────────┐              ╔╝
  --      ╚╗          │           λ   └┐           ╔╝
  --       ╚═════>  (1X)1  ═════════>  1(X1)  ═════╝
  --       σ⊗id                α                id⊗σ

  braiding-coherence⊗unit : [ (X ⊗₀ unit) ⊗₀ unit ⇒ X ⊗₀ unit ]⟨
                              σ⇒ ⊗₁ id            ⇒⟨ (unit ⊗₀ X) ⊗₀ unit ⟩
                              λ⇒ ⊗₁ id
                            ≈ ρ⇒ ⊗₁ id
                            ⟩
  braiding-coherence⊗unit = cancel-fromˡ braiding.FX≅GX (begin
    σ⇒ ∘ λ⇒ ⊗₁ id ∘ σ⇒ ⊗₁ id            ≈⟨ pullˡ (⟺ (glue◽◃ unitorˡ-commute-from coherence₁)) ⟩
    (λ⇒ ∘ id ⊗₁ σ⇒ ∘ α⇒) ∘ σ⇒ ⊗₁ id     ≈⟨ assoc²βε ⟩
    λ⇒ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id       ≈⟨ refl⟩∘⟨ hexagon₁ ⟩
    λ⇒ ∘ α⇒ ∘ σ⇒ ∘ α⇒                   ≈⟨ pullˡ coherence₁ ⟩
    λ⇒ ⊗₁ id ∘ σ⇒ ∘ α⇒                  ≈˘⟨ pushˡ (braiding.⇒.commute _) ⟩
    (σ⇒ ∘ id ⊗₁ λ⇒) ∘ α⇒                ≈⟨ pullʳ triangle ⟩
    σ⇒ ∘ ρ⇒ ⊗₁ id                       ∎)

  ρ⇒-α⇐ : id {X} ⊗₁ ρ⇒ {Y} ≈ ρ⇒ ∘ α⇐
  ρ⇒-α⇐ = switch-fromtoʳ associator coherence₂

  λ⇒-α⇐ : id {X} ⊗₁ λ⇒ {Y} ≈ ρ⇒ ⊗₁ id ∘ α⇐
  λ⇒-α⇐ = switch-fromtoʳ associator triangle

  braiding-coherence⊗unit′ : [ unit ⊗₀ (unit ⊗₀ X) ⇒ unit ⊗₀ X ]⟨
                               id ⊗₁ σ⇒            ⇒⟨ unit ⊗₀ (X ⊗₀ unit) ⟩
                               id ⊗₁ ρ⇒
                             ≈ id ⊗₁ λ⇒
                             ⟩
  braiding-coherence⊗unit′ = cancel-fromˡ braiding.FX≅GX (begin
    σ⇒ ∘ id ⊗₁ ρ⇒ ∘ id ⊗₁ σ⇒         ≈⟨ pullˡ (⟺ (glue◽◃ unitorʳ-commute-from (⟺ ρ⇒-α⇐))) ⟩
    (ρ⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒  ≈⟨ assoc ⟩
    ρ⇒ ∘ (σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒  ≈⟨ refl⟩∘⟨ hexagon₂ ⟩
    ρ⇒ ∘ (α⇐ ∘ σ⇒) ∘ α⇐              ≈⟨ refl⟩∘⟨ assoc ⟩
    ρ⇒ ∘ α⇐ ∘ σ⇒ ∘ α⇐                ≈⟨ pullˡ (⟺ ρ⇒-α⇐) ⟩
    id ⊗₁ ρ⇒ ∘ σ⇒ ∘ α⇐               ≈˘⟨ pushˡ σ⇒-comm ⟩
    (σ⇒ ∘ ρ⇒ ⊗₁ id) ∘ α⇐             ≈⟨ pullʳ (⟺ λ⇒-α⇐) ⟩
    σ⇒ ∘ id ⊗₁ λ⇒                    ∎)

-- The desired theorem follows from |braiding-coherence⊗unit| by
-- translating it along the right unitor (which is a natural iso).

braiding-coherence : [ X ⊗₀ unit ⇒ X ]⟨
                       σ⇒              ⇒⟨ unit ⊗₀ X ⟩
                       λ⇒
                     ≈ ρ⇒
                     ⟩
braiding-coherence = push-eq unitorʳ-naturalIsomorphism (begin
  (λ⇒ ∘ σ⇒) ⊗₁ id           ≈⟨ homomorphism ⟩
  (λ⇒ ⊗₁ id) ∘ (σ⇒ ⊗₁ id)   ≈⟨ braiding-coherence⊗unit ⟩
  ρ⇒  ⊗₁ id                 ∎)
  where open Functor (-⊗ unit)

-- The unit is transparent to the braiding on the left as well.  Same translation,
-- along the left unitor this time.

braiding-coherence′ : [ unit ⊗₀ X ⇒ X ]⟨
                        σ⇒              ⇒⟨ X ⊗₀ unit ⟩
                        ρ⇒
                      ≈ λ⇒
                      ⟩
braiding-coherence′ = push-eq unitorˡ-naturalIsomorphism (begin
  id ⊗₁ (ρ⇒ ∘ σ⇒)           ≈⟨ homomorphism ⟩
  (id ⊗₁ ρ⇒) ∘ (id ⊗₁ σ⇒)   ≈⟨ braiding-coherence⊗unit′ ⟩
  id ⊗₁ λ⇒                  ∎)
  where open Functor (unit ⊗-)

-- Variants of the hexagon identities defined on isos.

hexagon₁-iso : idᵢ ⊗ᵢ σ ∘ᵢ associator ∘ᵢ σ {X , Y} ⊗ᵢ idᵢ {Z} ≈ᵢ
               associator ∘ᵢ σ {X , Y ⊗₀ Z} ∘ᵢ associator
hexagon₁-iso = ⌞ hexagon₁ ⌟

hexagon₁-inv : (σ⇐ {X} {Y} ⊗₁ id {Z} ∘ α⇐) ∘ id ⊗₁ σ⇐ ≈
               (α⇐ ∘ σ⇐ {X} {Y ⊗₀ Z}) ∘ α⇐
hexagon₁-inv = to-≈ hexagon₁-iso

hexagon₂-iso : (σ ⊗ᵢ idᵢ ∘ᵢ associator ⁻¹) ∘ᵢ idᵢ {X} ⊗ᵢ σ {Y , Z} ≈ᵢ
               (associator ⁻¹ ∘ᵢ σ {X ⊗₀ Y , Z}) ∘ᵢ associator ⁻¹
hexagon₂-iso = ⌞ hexagon₂ ⌟

hexagon₂-inv : id {X} ⊗₁ σ⇐ {Y} {Z} ∘ α⇒ ∘ σ⇐ ⊗₁ id ≈
               α⇒ ∘ σ⇐ {X ⊗₀ Y} {Z} ∘ α⇒
hexagon₂-inv = to-≈ hexagon₂-iso

-- Variants of the above coherence law.

braiding-coherence-iso : unitorˡ ∘ᵢ σ ≈ᵢ unitorʳ {X}
braiding-coherence-iso = ⌞ braiding-coherence ⌟

braiding-coherence-iso′ : unitorʳ ∘ᵢ σ ≈ᵢ unitorˡ {X}
braiding-coherence-iso′ = ⌞ braiding-coherence′ ⌟

braiding-coherence-inv : σ⇐ ∘ λ⇐ ≈ ρ⇐ {X}
braiding-coherence-inv = to-≈ braiding-coherence-iso

braiding-coherence-inv′ : σ⇐ ∘ ρ⇐ ≈ λ⇐ {X}
braiding-coherence-inv′ = to-≈ braiding-coherence-iso′

-- ... and the same two, solved for the braiding itself.

braiding-coherence-σ : σ⇒ {X} {unit} ≈ λ⇐ ∘ ρ⇒
braiding-coherence-σ = switch-fromtoˡ unitorˡ braiding-coherence

braiding-coherence-σ′ : σ⇒ {unit} {X} ≈ ρ⇐ ∘ λ⇒
braiding-coherence-σ′ = switch-fromtoˡ unitorʳ braiding-coherence′

-- The inverse of the braiding is also a braiding on M.

inv-Braided : Braided M
inv-Braided = record
  { braiding = ≃.sym (flip-bifunctor-NI braiding)
  ; hexagon₁ = hexagon₂-inv
  ; hexagon₂ = hexagon₁-inv
  }

-- The opposite monoidal category is braided.

braided-Op : Braided monoidal-Op
braided-Op = record
    { braiding = braiding.op′
    ; hexagon₁ = hexagon₁-inv
    ; hexagon₂ = hexagon₂-inv
    }

-- The inverse of the braiding is also a braiding on the opposite monoidal category.

inv-braided-Op : Braided monoidal-Op
inv-braided-Op = record
    { braiding = ≃.sym (flip-bifunctor-NI braiding.op′)
    ; hexagon₁ = hexagon₂
    ; hexagon₂ = hexagon₁
    }

-- A variant of the above coherence law for the inverse of the braiding.

inv-braiding-coherence : [ unit ⊗₀ X ⇒ X ]⟨
                           σ⇐            ⇒⟨ X ⊗₀ unit ⟩
                           ρ⇒
                         ≈ λ⇒
                         ⟩
inv-braiding-coherence = ⟺ (switch-fromtoʳ σ braiding-coherence)

-- Reversing a ternary product via braiding commutes with the associator.

assoc-reverse : [ X ⊗₀ (Y ⊗₀ Z) ⇒ (X ⊗₀ Y) ⊗₀ Z ]⟨
                  id ⊗₁ σ⇒      ⇒⟨ X ⊗₀ (Z ⊗₀ Y) ⟩
                  σ⇒            ⇒⟨ (Z ⊗₀ Y) ⊗₀ X ⟩
                  α⇒            ⇒⟨ Z ⊗₀ (Y ⊗₀ X) ⟩
                  id ⊗₁ σ⇐      ⇒⟨ Z ⊗₀ (X ⊗₀ Y) ⟩
                  σ⇐
                ≈ α⇐
                ⟩
assoc-reverse = begin
  σ⇐ ∘ id ⊗₁ σ⇐ ∘ α⇒ ∘ σ⇒ ∘ id ⊗₁ σ⇒    ≈⟨ refl⟩∘⟨ assoc²εβ ⟩
  σ⇐ ∘ (id ⊗₁ σ⇐ ∘ α⇒ ∘ σ⇒) ∘ id ⊗₁ σ⇒  ≈⟨ refl⟩∘⟨ pushˡ hex₁' ⟩
  σ⇐ ∘ (α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ σ⇒  ≈⟨ refl⟩∘⟨ pullʳ (sym-assoc ○ hexagon₂) ⟩
  σ⇐ ∘ α⇒ ∘ (α⇐ ∘ σ⇒) ∘ α⇐              ≈⟨ refl⟩∘⟨ pullˡ (cancelˡ associator.isoʳ) ⟩
  σ⇐ ∘ σ⇒ ∘ α⇐                          ≈⟨ cancelˡ (braiding.iso.isoˡ _) ⟩
  α⇐                                    ∎
  where
    hex₁' = conjugate-from associator (idᵢ ⊗ᵢ σ) (⟺ (hexagon₁ ○ sym-assoc))

-- Scalars are central: the left and right actions of a scalar on any morphism agree in a
-- braided monoidal category. Conjugating |f ⊗₁ s| by the braiding swaps the two tensor factors,
-- and |braiding-coherence| identifies the two unitor sandwiches |ρ …| and |λ …|.

scalar-central : {f : X ⇒ Y} {s : Scalar} → f ·ʳ s ≈ s ·ˡ f
scalar-central {f = f} {s = s} = begin
  ρ⇒ ∘ (f ⊗₁ s) ∘ ρ⇐                ≈˘⟨ braiding-coherence ⟩∘⟨ refl⟩∘⟨ braiding-coherence-inv ⟩
  (λ⇒ ∘ σ⇒) ∘ (f ⊗₁ s) ∘ (σ⇐ ∘ λ⇐)  ≈⟨ assoc ⟩
  λ⇒ ∘ σ⇒ ∘ (f ⊗₁ s) ∘ (σ⇐ ∘ λ⇐)    ≈⟨ refl⟩∘⟨ pullˡ σ⇒-comm ⟩
  λ⇒ ∘ ((s ⊗₁ f) ∘ σ⇒) ∘ (σ⇐ ∘ λ⇐)  ≈⟨ refl⟩∘⟨ cancelInner (braiding.iso.isoʳ _) ⟩
  λ⇒ ∘ (s ⊗₁ f) ∘ λ⇐                ∎

-- The monoid of objects is commutative up to the braiding isomorphism.

Obj-⊗-Comm-Monoid : CommutativeMonoid _ _
Obj-⊗-Comm-Monoid = record
  { Carrier = Obj
  ; _≈_ = _≅_
  ; _∙_ = _⊗₀_
  ; ε   = unit
  ; isCommutativeMonoid = record
    { isMonoid = Monoid.isMonoid Obj-⊗-Monoid
    ; comm     = λ X Y → σ {X , Y}
    }
  }
