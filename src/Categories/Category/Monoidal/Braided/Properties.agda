{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided using (Braided)

module Categories.Category.Monoidal.Braided.Properties
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (BM : Braided M) where

open import Data.Product using (_,_)

import Categories.Category.Construction.Core C as Core
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
import Categories.Category.Monoidal.Utilities M as MonoidalUtilities
open import Categories.Functor using (Functor)
open import Categories.Morphism.Reasoning C hiding (push-eq)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
  using (push-eq)

open Category C
open Commutation C
open Braided BM
open MonoidalUtilities using (_⊗ᵢ_; unitorʳ-naturalIsomorphism)
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
    (λ⇒ ∘ id ⊗₁ σ⇒ ∘ α⇒) ∘ σ⇒ ⊗₁ id     ≈⟨ assoc²' ⟩
    λ⇒ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗₁ id       ≈⟨ refl⟩∘⟨ hexagon₁ ⟩
    λ⇒ ∘ α⇒ ∘ σ⇒ ∘ α⇒                   ≈⟨ pullˡ coherence₁ ⟩
    λ⇒ ⊗₁ id ∘ σ⇒ ∘ α⇒                  ≈˘⟨ pushˡ (braiding.⇒.commute _) ⟩
    (σ⇒ ∘ id ⊗₁ λ⇒) ∘ α⇒                ≈⟨ pullʳ triangle ⟩
    σ⇒ ∘ ρ⇒ ⊗₁ id                       ∎)

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

braiding-coherence-inv : σ⇐ ∘ λ⇐ ≈ ρ⇐ {X}
braiding-coherence-inv = to-≈ braiding-coherence-iso

-- The inverse of the braiding is also a braiding on M.

inv-Braided : Braided M
inv-Braided = record
  { braiding = niHelper (record
    { η       = λ _ → σ⇐
    ; η⁻¹     = λ _ → σ⇒
    ; commute = λ{ (f , g) → braiding.⇐.commute (g , f) }
    ; iso     = λ{ (X , Y) → record
      { isoˡ = braiding.iso.isoʳ (Y , X)
      ; isoʳ = braiding.iso.isoˡ (Y , X) } }
    })
  ; hexagon₁ = hexagon₂-inv
  ; hexagon₂ = hexagon₁-inv
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
  σ⇐ ∘ id ⊗₁ σ⇐ ∘ α⇒ ∘ σ⇒ ∘ id ⊗₁ σ⇒    ≈˘⟨ refl⟩∘⟨ assoc²' ⟩
  σ⇐ ∘ (id ⊗₁ σ⇐ ∘ α⇒ ∘ σ⇒) ∘ id ⊗₁ σ⇒  ≈⟨ refl⟩∘⟨ pushˡ hex₁' ⟩
  σ⇐ ∘ (α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ σ⇒  ≈⟨ refl⟩∘⟨ pullʳ (sym-assoc ○ hexagon₂) ⟩
  σ⇐ ∘ α⇒ ∘ (α⇐ ∘ σ⇒) ∘ α⇐              ≈⟨ refl⟩∘⟨ pullˡ (cancelˡ associator.isoʳ) ⟩
  σ⇐ ∘ σ⇒ ∘ α⇐                          ≈⟨ cancelˡ (braiding.iso.isoˡ _) ⟩
  α⇐                                    ∎
  where
    hex₁' = conjugate-from associator (idᵢ ⊗ᵢ σ) (⟺ (hexagon₁ ○ sym-assoc))
