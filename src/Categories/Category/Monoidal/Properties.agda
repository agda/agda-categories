{-# OPTIONS --without-K --safe #-}
open import Categories.Category
import Categories.Category.Monoidal as M

-- Properties of Monoidal Categories

module Categories.Category.Monoidal.Properties
  {o ℓ e} {C : Category o ℓ e} (MC : M.Monoidal C) where

open import Data.Product using (_,_; Σ; uncurry′)

open Category C
open M.Monoidal MC
open import Categories.Category.Monoidal.Utilities MC
import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.Category.Construction.Core C as Core using (Core)
open import Categories.Category.Product using (Product)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Properties
open import Categories.Morphism.Isomorphism C
  using (elim-triangleˡ′; triangle-prism; cut-squareʳ)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
  using (push-eq)

private
  module C = Category C
  variable
    A B : Obj
open Core.Shorthands

⊗-iso : Bifunctor Core Core Core
⊗-iso = record
  { F₀           = uncurry′ _⊗₀_
  ; F₁           =  λ where (f , g) → f ⊗ᵢ g
  ; identity     = refl⊗refl≃refl
  ; homomorphism = ⌞ homomorphism ⌟
  ; F-resp-≈     = λ where (⌞ eq₁ ⌟ , ⌞ eq₂ ⌟) → ⌞ F-resp-≈ (eq₁ , eq₂) ⌟
  }
  where open Functor ⊗

_⊗ᵢ- : Obj → Functor Core Core
X ⊗ᵢ- = appˡ ⊗-iso X

-⊗ᵢ_ : Obj → Functor Core Core
-⊗ᵢ X = appʳ ⊗-iso X

-- Coherence laws due to Mac Lane (1963) that were subsequently proven
-- admissible by Max Kelly (1964).  See
-- https://ncatlab.org/nlab/show/monoidal+category#other_coherence_conditions
-- for more details.

module Kelly's where
  open Functor
  open Shorthands
  open Commutation C
  open Commutationᵢ

  private
    variable
      f f′ g h h′ i i′ j k : A ≅ B

  module _ {X Y : Obj} where
    open HomReasoningᵢ

    -- TS: following three isos commute

    ua : unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ unit ⊗₀ X ⊗₀ Y
    ua = idᵢ ⊗ᵢ associator

    u[λY] : unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y
    u[λY] = idᵢ ⊗ᵢ unitorˡ ⊗ᵢ idᵢ

    uλ : unit ⊗₀ unit ⊗₀ X ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y
    uλ = idᵢ ⊗ᵢ unitorˡ

    -- setups

    perimeter : [ ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y ]⟨
                  (unitorʳ ⊗ᵢ idᵢ) ⊗ᵢ idᵢ    ≅⟨ (unit ⊗₀ X) ⊗₀ Y ⟩
                  associator
                ≈ associator                 ≅⟨ (unit ⊗₀ unit) ⊗₀ X ⊗₀ Y ⟩
                  associator                 ≅⟨ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ⟩
                  uλ
                ⟩
    perimeter = ⟺ (glue◃◽′ triangle-iso
                             (⟺ ⌞ Equiv.trans assoc-commute-from
                                                (∘-resp-≈ˡ (F-resp-≈ ⊗ (Equiv.refl , identity ⊗))) ⌟))
      where open MR Core

    [uλ]Y : (unit ⊗₀ (unit ⊗₀ X)) ⊗₀ Y ≅ (unit ⊗₀ X) ⊗₀ Y
    [uλ]Y = (idᵢ ⊗ᵢ unitorˡ) ⊗ᵢ idᵢ

    aY : ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ (unit ⊗₀ unit ⊗₀ X) ⊗₀ Y
    aY = associator ⊗ᵢ idᵢ

    [ρX]Y : ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ (unit ⊗₀ X) ⊗₀ Y
    [ρX]Y = (unitorʳ ⊗ᵢ idᵢ) ⊗ᵢ idᵢ

    tri : [uλ]Y ∘ᵢ aY ≈ᵢ [ρX]Y
    tri = ⌞ [ appʳ ⊗ Y ]-resp-∘ triangle ⌟

    sq : associator ∘ᵢ [uλ]Y ≈ᵢ u[λY] ∘ᵢ associator
    sq = ⌞ assoc-commute-from ⌟

    -- proofs

    perimeter′ : [ ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y ]⟨
                   (unitorʳ ⊗ᵢ idᵢ) ⊗ᵢ idᵢ    ≅⟨ (unit ⊗₀ X) ⊗₀ Y ⟩
                   associator
                 ≈ aY                         ≅⟨ (unit ⊗₀ (unit ⊗₀ X)) ⊗₀ Y ⟩
                   associator                 ≅⟨ unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ⟩
                   ua                         ≅⟨ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ⟩
                   uλ
                 ⟩
    perimeter′ = begin
      associator ∘ᵢ (unitorʳ ⊗ᵢ idᵢ) ⊗ᵢ idᵢ    ≈⟨ perimeter ⟩
      uλ ∘ᵢ associator ∘ᵢ associator           ≈˘⟨ refl⟩∘⟨ pentagon-iso ⟩
      uλ ∘ᵢ ua ∘ᵢ associator ∘ᵢ aY             ∎

    top-face : uλ ∘ᵢ ua ≈ᵢ u[λY]
    top-face = elim-triangleˡ′ (⟺ perimeter′) (glue◽◃ (⟺ sq) tri)
      where open MR Core

    coherence-iso₁ : [ (unit ⊗₀ X) ⊗₀ Y ≅ X ⊗₀ Y ]⟨
                       associator       ≅⟨ unit ⊗₀ X ⊗₀ Y ⟩
                       unitorˡ
                     ≈ unitorˡ ⊗ᵢ idᵢ
                     ⟩
    coherence-iso₁ = triangle-prism top-face square₁ square₂ square₃
      where square₁ : [ unit ⊗₀ X ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y ]⟨
                        unitorˡ ⁻¹ ∘ᵢ unitorˡ
                      ≈ idᵢ ⊗ᵢ unitorˡ ∘ᵢ unitorˡ ⁻¹
                      ⟩
            square₁ = ⌞ unitorˡ-commute-to ⌟

            square₂ : [ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ]⟨
                        unitorˡ ⁻¹ ∘ᵢ associator
                      ≈ idᵢ ⊗ᵢ associator ∘ᵢ unitorˡ ⁻¹
                      ⟩
            square₂ = ⌞ unitorˡ-commute-to ⌟

            square₃ : [ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y ]⟨
                        unitorˡ ⁻¹ ∘ᵢ unitorˡ ⊗ᵢ idᵢ
                      ≈ idᵢ ⊗ᵢ unitorˡ ⊗ᵢ idᵢ ∘ᵢ unitorˡ ⁻¹
                      ⟩
            square₃ = ⌞ unitorˡ-commute-to ⌟

    coherence₁ : [ (unit ⊗₀ X) ⊗₀ Y ⇒ X ⊗₀ Y ]⟨
                   α⇒               ⇒⟨ unit ⊗₀ X ⊗₀ Y ⟩
                   λ⇒
                 ≈ λ⇒ ⊗₁ id
                 ⟩
    coherence₁ = from-≈ coherence-iso₁

    coherence-inv₁ : [ X ⊗₀ Y ⇒ (unit ⊗₀ X) ⊗₀ Y ]⟨
                       λ⇐               ⇒⟨ unit ⊗₀ X ⊗₀ Y ⟩
                       α⇐
                     ≈ λ⇐ ⊗₁ id
                     ⟩
    coherence-inv₁ = to-≈ coherence-iso₁

    -- another coherence property

    -- TS : the following three commute

    ρu : ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y) ⊗₀ unit
    ρu = unitorʳ ⊗ᵢ idᵢ

    au : ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit
    au = associator ⊗ᵢ idᵢ

    [Xρ]u : (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y) ⊗₀ unit
    [Xρ]u = (idᵢ ⊗ᵢ unitorʳ) ⊗ᵢ idᵢ


    perimeter″ : [ ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ X ⊗₀ Y ⊗₀ unit ]⟨
                   associator                 ≅⟨ (X ⊗₀ Y) ⊗₀ unit ⊗₀ unit ⟩
                   associator                 ≅⟨ X ⊗₀ Y ⊗₀ unit ⊗₀ unit ⟩
                   idᵢ ⊗ᵢ idᵢ ⊗ᵢ unitorˡ
                 ≈ ρu                         ≅⟨ (X ⊗₀ Y) ⊗₀ unit ⟩
                   associator
                 ⟩
    perimeter″ = glue▹◽ triangle-iso (⟺ ⌞
        Equiv.trans (∘-resp-≈ʳ (F-resp-≈ ⊗ (Equiv.sym (identity ⊗) , Equiv.refl)))
                     assoc-commute-from ⌟)
      where open MR Core

    perimeter‴ : [ ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ X ⊗₀ Y ⊗₀ unit  ]⟨
                   associator ⊗ᵢ idᵢ          ≅⟨ (X ⊗₀ (Y ⊗₀ unit)) ⊗₀ unit ⟩
                   (associator                ≅⟨ X ⊗₀ (Y ⊗₀ unit) ⊗₀ unit ⟩
                   idᵢ ⊗ᵢ associator          ≅⟨ X ⊗₀ Y ⊗₀ unit ⊗₀ unit ⟩
                   idᵢ ⊗ᵢ idᵢ ⊗ᵢ unitorˡ)
                 ≈ ρu                         ≅⟨ (X ⊗₀ Y) ⊗₀ unit ⟩
                   associator
                 ⟩
    perimeter‴ = let α = associator in let λλ = unitorˡ in begin
      (idᵢ ⊗ᵢ idᵢ ⊗ᵢ λλ ∘ᵢ idᵢ ⊗ᵢ α ∘ᵢ α) ∘ᵢ α ⊗ᵢ idᵢ  ≈⟨ ⌞ assoc ⌟ ⟩
       idᵢ ⊗ᵢ idᵢ ⊗ᵢ λλ ∘ᵢ (idᵢ ⊗ᵢ α ∘ᵢ α) ∘ᵢ α ⊗ᵢ idᵢ ≈⟨ refl⟩∘⟨ ⌞ assoc ⌟ ⟩
       idᵢ ⊗ᵢ idᵢ ⊗ᵢ λλ ∘ᵢ idᵢ ⊗ᵢ α ∘ᵢ α ∘ᵢ α ⊗ᵢ idᵢ   ≈⟨ refl⟩∘⟨ pentagon-iso ⟩
       idᵢ ⊗ᵢ idᵢ ⊗ᵢ λλ ∘ᵢ α ∘ᵢ α                      ≈⟨ perimeter″ ⟩
       α ∘ᵢ ρu                                         ∎

    top-face′ : [Xρ]u ∘ᵢ au ≈ᵢ ρu
    top-face′ = cut-squareʳ perimeter‴ (⟺ (glue◃◽′ tri′ (⟺ ⌞ assoc-commute-from ⌟)))
      where open MR Core
            tri′ : [ X ⊗₀ (Y ⊗₀ unit) ⊗₀ unit ≅ X ⊗₀ Y ⊗₀ unit ]⟨
                     (idᵢ ⊗ᵢ idᵢ ⊗ᵢ unitorˡ ∘ᵢ idᵢ ⊗ᵢ associator)
                   ≈ idᵢ ⊗ᵢ unitorʳ ⊗ᵢ idᵢ
                   ⟩
            tri′ = ⌞ [ X ⊗- ]-resp-∘ triangle ⌟

    coherence-iso₂ : [ (X ⊗₀ Y) ⊗₀ unit ≅ X ⊗₀ Y ]⟨
                       idᵢ ⊗ᵢ unitorʳ ∘ᵢ associator
                     ≈ unitorʳ
                     ⟩
    coherence-iso₂ = triangle-prism top-face′ square₁ square₂ ⌞ unitorʳ-commute-to ⌟
      where square₁ : [ X ⊗₀ Y ⊗₀ unit ≅ (X ⊗₀ Y) ⊗₀ unit ]⟨
                        unitorʳ ⁻¹ ∘ᵢ idᵢ ⊗ᵢ unitorʳ
                      ≈ (idᵢ ⊗ᵢ unitorʳ) ⊗ᵢ idᵢ ∘ᵢ unitorʳ ⁻¹
                      ⟩
            square₁ = ⌞ unitorʳ-commute-to ⌟

            square₂ : [ (X ⊗₀ Y) ⊗₀ unit ≅ (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit ]⟨
                        unitorʳ ⁻¹ ∘ᵢ associator
                      ≈ associator ⊗ᵢ idᵢ ∘ᵢ unitorʳ ⁻¹
                      ⟩
            square₂ = ⌞ unitorʳ-commute-to ⌟

    coherence₂ : [ (X ⊗₀ Y) ⊗₀ unit ⇒ X ⊗₀ Y ]⟨
                   α⇒               ⇒⟨ X ⊗₀ (Y ⊗₀ unit) ⟩
                   id ⊗₁ ρ⇒
                 ≈ ρ⇒
                 ⟩
    coherence₂ = from-≈ coherence-iso₂

    coherence-inv₂ : [ X ⊗₀ Y      ⇒ (X ⊗₀ Y) ⊗₀ unit ]⟨
                       id ⊗₁ ρ⇐    ⇒⟨ X ⊗₀ (Y ⊗₀ unit) ⟩
                       α⇐
                     ≈ ρ⇐
                     ⟩
    coherence-inv₂ = to-≈ coherence-iso₂

  -- A third coherence condition (Lemma 2.3)

  coherence₃ : [ unit ⊗₀ unit ⇒ unit ]⟨ λ⇒ ≈ ρ⇒ ⟩
  coherence₃ = push-eq unitorˡ-naturalIsomorphism (begin
    C.id ⊗₁ λ⇒               ≈˘⟨ cancelʳ associator.isoʳ ⟩
    (C.id ⊗₁ λ⇒ ∘ α⇒) ∘ α⇐   ≈⟨ triangle ⟩∘⟨refl ⟩
    ρ⇒ ⊗₁ C.id ∘ α⇐          ≈⟨ unitor-coherenceʳ ⟩∘⟨refl ⟩
    ρ⇒ ∘ α⇐                  ≈˘⟨ coherence₂ ⟩∘⟨refl ⟩
    (C.id ⊗₁ ρ⇒ ∘ α⇒) ∘ α⇐   ≈⟨ cancelʳ associator.isoʳ ⟩
    C.id ⊗₁ ρ⇒               ∎)
    where
      open MR C hiding (push-eq)
      open C.HomReasoning

  coherence-iso₃ : [ unit ⊗₀ unit ≅ unit ]⟨ unitorˡ ≈ unitorʳ ⟩
  coherence-iso₃ = ⌞ coherence₃ ⌟

  coherence-inv₃ : [ unit ⇒ unit ⊗₀ unit ]⟨ λ⇐ ≈ ρ⇐ ⟩
  coherence-inv₃ = to-≈ coherence-iso₃

open Kelly's public using
  ( coherence₁; coherence-iso₁; coherence-inv₁
  ; coherence₂; coherence-iso₂; coherence-inv₂
  ; coherence₃; coherence-iso₃; coherence-inv₃
  )
