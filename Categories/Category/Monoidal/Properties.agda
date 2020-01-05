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
open import Categories.Category.Construction.Core C
open import Categories.Category.Product using (Product)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Properties
open import Categories.Category.Groupoid using (IsGroupoid)
open import Categories.Morphism C
open import Categories.Morphism.IsoEquiv C using (_≃_; ⌞_⌟)
open import Categories.Morphism.Isomorphism C
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
  using (push-eq)

private
  module C = Category C
  variable
    A B : Obj

⊗-iso : Bifunctor Core Core Core
⊗-iso = record
  { F₀           = uncurry′ _⊗₀_
  ; F₁           =  λ where (f , g) → f ⊗ᵢ g
  ; identity     = refl⊗refl≃refl
  ; homomorphism = ⌞ homomorphism ⌟
  ; F-resp-≈     = λ where (⌞ eq₁ ⌟ , ⌞ eq₂ ⌟) → ⌞ F-resp-≈ (eq₁ , eq₂) ⌟
  }
  where open Functor ⊗
        open _≃_

_⊗ᵢ- : Obj → Functor Core Core
X ⊗ᵢ- = appˡ ⊗-iso X

-⊗ᵢ_ : Obj → Functor Core Core
-⊗ᵢ X = appʳ ⊗-iso X

-- Parallel-to-serial conversions and splitting of ∘ across ⊗

module Serialize where
  open MonR MC
  -- Parallel-to-serial conversions
  --
  --   |   |        |   |       |   |
  --   |   |        |  [g]     [f]  |
  --  [f] [g]   =   |   |   =   |   |
  --   |   |       [f]  |       |  [g]
  --   |   |        |   |       |   |

  serialize₁₂ : ∀ {X₁ Y₁ X₂ Y₂} {f : X₁ ⇒ Y₁} {g : X₂ ⇒ Y₂} →
                f ⊗₁ g ≈ f ⊗₁ C.id ∘ C.id ⊗₁ g
  serialize₁₂ {f = f} {g} = begin
    f ⊗₁ g                     ≈˘⟨ identityʳ ⟩⊗⟨ identityˡ ⟩
    (f ∘ C.id) ⊗₁ (C.id ∘ g)   ≈⟨ ⊗-distrib-over-∘ ⟩
    f ⊗₁ C.id ∘ C.id ⊗₁ g      ∎

  serialize₂₁ : ∀ {X₁ Y₁ X₂ Y₂} {f : X₁ ⇒ Y₁} {g : X₂ ⇒ Y₂} →
                f ⊗₁ g ≈ id ⊗₁ g ∘ f ⊗₁ C.id
  serialize₂₁ {f = f} {g} = begin
    f ⊗₁ g                     ≈˘⟨ identityˡ ⟩⊗⟨ identityʳ ⟩
    (C.id ∘ f) ⊗₁ (g ∘ C.id)   ≈⟨ ⊗-distrib-over-∘ ⟩
    C.id ⊗₁ g ∘ f ⊗₁ C.id      ∎

  -- Split a composite in the first component
  --
  --   |   |        |   |       |   |
  --  [g]  |       [g]  |      [g] [h]
  --   |  [h]   =   |   |   =   |   |
  --  [f]  |       [f] [h]     [f]  |
  --   |   |        |   |       |   |

  split₁ʳ : ∀ {X₁ Y₁ Z₁ X₂ Y₂} {f : Y₁ ⇒ Z₁} {g : X₁ ⇒ Y₁} {h : X₂ ⇒ Y₂} →
            (f ∘ g) ⊗₁ h ≈ f ⊗₁ h ∘ g ⊗₁ C.id
  split₁ʳ {f = f} {g} {h} = begin
    (f ∘ g) ⊗₁ h            ≈˘⟨ refl⟩⊗⟨ identityʳ ⟩
    (f ∘ g) ⊗₁ (h ∘ C.id)   ≈⟨ ⊗-distrib-over-∘ ⟩
    f ⊗₁ h ∘ g ⊗₁ C.id      ∎

  split₁ˡ : ∀ {X₁ Y₁ Z₁ X₂ Y₂} {f : Y₁ ⇒ Z₁} {g : X₁ ⇒ Y₁} {h : X₂ ⇒ Y₂} →
            (f ∘ g) ⊗₁ h ≈ f ⊗₁ C.id ∘ g ⊗₁ h
  split₁ˡ {f = f} {g} {h} = begin
    (f ∘ g) ⊗₁ h            ≈˘⟨ refl⟩⊗⟨ identityˡ ⟩
    (f ∘ g) ⊗₁ (C.id ∘ h)   ≈⟨ ⊗-distrib-over-∘ ⟩
    f ⊗₁ C.id ∘ g ⊗₁ h      ∎

  -- Split a composite in the second component
  --
  --   |   |        |   |       |   |
  --   |  [h]       |  [h]     [f] [h]
  --  [f]  |    =   |   |   =   |   |
  --   |  [g]      [f] [g]      |  [g]
  --   |   |        |   |       |   |

  split₂ʳ : ∀ {X₁ Y₁ X₂ Y₂ Z₂} {f : X₁ ⇒ Y₁} {g : Y₂ ⇒ Z₂} {h : X₂ ⇒ Y₂} →
            f ⊗₁ (g ∘ h) ≈ f ⊗₁ g ∘ C.id ⊗₁ h
  split₂ʳ {f = f} {g} {h} = begin
    f ⊗₁ (g ∘ h)            ≈˘⟨ identityʳ ⟩⊗⟨refl ⟩
    (f ∘ C.id) ⊗₁ (g ∘ h)   ≈⟨ ⊗-distrib-over-∘ ⟩
    f ⊗₁ g ∘ C.id ⊗₁ h      ∎

  split₂ˡ : ∀ {X₁ Y₁ X₂ Y₂ Z₂} {f : X₁ ⇒ Y₁} {g : Y₂ ⇒ Z₂} {h : X₂ ⇒ Y₂} →
            f ⊗₁ (g ∘ h) ≈ C.id ⊗₁ g ∘ f ⊗₁ h
  split₂ˡ {f = f} {g} {h} = begin
    f ⊗₁ (g ∘ h)            ≈˘⟨ identityˡ ⟩⊗⟨refl ⟩
    (C.id ∘ f) ⊗₁ (g ∘ h)   ≈⟨ ⊗-distrib-over-∘ ⟩
    C.id ⊗₁ g ∘ f ⊗₁ h      ∎

open Serialize public

-- Coherence laws due to Mac Lane (1963) the were subsequently proven
-- admissible by Max Kelly (1964).  See
-- https://ncatlab.org/nlab/show/monoidal+category#other_coherence_conditions
-- for more details.

module Kelly's where
  open Functor
  open IsGroupoid.Commutation Core-isGroupoid

  private
    assoc′ = IsGroupoid.assoc Core-isGroupoid
    variable
          f f′ g h h′ i i′ j k : A ≅ B

  module _ {X Y : Obj} where
    open IsGroupoid.HomReasoning Core-isGroupoid

    -- TS: following three isos commute

    ua : unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ unit ⊗₀ X ⊗₀ Y
    ua = ≅.refl ⊗ᵢ associator

    u[λY] : unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y
    u[λY] = ≅.refl ⊗ᵢ unitorˡ ⊗ᵢ ≅.refl

    uλ : unit ⊗₀ unit ⊗₀ X ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y
    uλ = ≅.refl ⊗ᵢ unitorˡ

    -- setups

    perimeter : [ ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                  (unitorʳ ⊗ᵢ ≅.refl) ⊗ᵢ ≅.refl               ⇒⟨ (unit ⊗₀ X) ⊗₀ Y ⟩
                  associator
                ≈ associator                                  ⇒⟨ (unit ⊗₀ unit) ⊗₀ X ⊗₀ Y ⟩
                  associator                                  ⇒⟨ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ⟩
                  uλ
                ⟩
    perimeter = ⟺ (glue◃◽′ triangle-iso
                             (sym (lift-square′ (Equiv.trans assoc-commute-from
                                                             (∘-resp-≈ˡ (F-resp-≈ ⊗ (Equiv.refl , identity ⊗)))))))
      where open MR Core

    [uλ]Y : (unit ⊗₀ (unit ⊗₀ X)) ⊗₀ Y ≅ (unit ⊗₀ X) ⊗₀ Y
    [uλ]Y = (≅.refl ⊗ᵢ unitorˡ) ⊗ᵢ ≅.refl

    aY : ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ (unit ⊗₀ unit ⊗₀ X) ⊗₀ Y
    aY = associator ⊗ᵢ ≅.refl

    [ρX]Y : ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ (unit ⊗₀ X) ⊗₀ Y
    [ρX]Y = (unitorʳ ⊗ᵢ ≅.refl) ⊗ᵢ ≅.refl

    tri : [uλ]Y ∘ᵢ aY ≃ [ρX]Y
    tri = lift-triangle′ ([ appʳ ⊗ Y ]-resp-∘ triangle)

    sq : associator ∘ᵢ [uλ]Y ≃ u[λY] ∘ᵢ associator
    sq = lift-square′ assoc-commute-from

    -- proofs

    perimeter′ : [ ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                   (unitorʳ ⊗ᵢ ≅.refl) ⊗ᵢ ≅.refl     ⇒⟨ (unit ⊗₀ X) ⊗₀ Y ⟩
                   associator
                 ≈ aY                                 ⇒⟨ (unit ⊗₀ (unit ⊗₀ X)) ⊗₀ Y ⟩
                   associator                         ⇒⟨ unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ⟩
                   ua                                 ⇒⟨ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ⟩
                   uλ
                 ⟩
    perimeter′ = begin
      associator ∘ᵢ (unitorʳ ⊗ᵢ ≅.refl) ⊗ᵢ ≅.refl    ≈⟨ perimeter ⟩
      uλ ∘ᵢ associator ∘ᵢ associator                  ≈˘⟨ refl⟩∘⟨ pentagon-iso ⟩
      uλ ∘ᵢ ua ∘ᵢ associator ∘ᵢ aY                    ∎

    top-face : uλ ∘ᵢ ua ≃ u[λY]
    top-face = elim-triangleˡ′ (sym perimeter′) (glue◽◃ (sym sq) tri)
      where open MR Core

    coherence-iso₁ : [ (unit ⊗₀ X) ⊗₀ Y ⇒ X ⊗₀ Y ]⟨
                    associator                ⇒⟨ unit ⊗₀ X ⊗₀ Y ⟩
                    unitorˡ
                  ≈ unitorˡ ⊗ᵢ ≅.refl
                  ⟩
    coherence-iso₁ = triangle-prism top-face square₁ square₂ square₃
      where square₁ : [ unit ⊗₀ X ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                        ≅.sym unitorˡ ∘ᵢ unitorˡ
                      ≈ ≅.refl ⊗ᵢ unitorˡ ∘ᵢ ≅.sym unitorˡ
                      ⟩
            square₁ = lift-square′ unitorˡ-commute-to

            square₂ : [ (unit ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ]⟨
                        ≅.sym unitorˡ ∘ᵢ associator
                      ≈ ≅.refl ⊗ᵢ associator ∘ᵢ ≅.sym unitorˡ
                      ⟩
            square₂ = lift-square′ unitorˡ-commute-to

            square₃ : [ (unit ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                        ≅.sym unitorˡ ∘ᵢ unitorˡ ⊗ᵢ ≅.refl
                      ≈ ≅.refl ⊗ᵢ unitorˡ ⊗ᵢ ≅.refl ∘ᵢ ≅.sym unitorˡ
                      ⟩
            square₃ = lift-square′ unitorˡ-commute-to

    coherence₁ : unitorˡ.from ∘ associator.from ≈ unitorˡ.from {X} ⊗₁ C.id {Y}
    coherence₁ = project-triangle coherence-iso₁

    -- another coherence property

    -- TS : the following three commute

    ρu : ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y) ⊗₀ unit
    ρu = unitorʳ ⊗ᵢ ≅.refl

    au : ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit
    au = associator ⊗ᵢ ≅.refl

    [Xρ]u : (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y) ⊗₀ unit
    [Xρ]u = (≅.refl ⊗ᵢ unitorʳ) ⊗ᵢ ≅.refl


    perimeter″ : [ ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ⇒ X ⊗₀ Y ⊗₀ unit ]⟨
                   associator                        ⇒⟨ (X ⊗₀ Y) ⊗₀ unit ⊗₀ unit ⟩
                   associator                        ⇒⟨ X ⊗₀ Y ⊗₀ unit ⊗₀ unit ⟩
                   ≅.refl ⊗ᵢ ≅.refl ⊗ᵢ unitorˡ
                 ≈ ρu                                ⇒⟨ (X ⊗₀ Y) ⊗₀ unit ⟩
                   associator
                 ⟩
    perimeter″ = glue▹◽ triangle-iso (sym (lift-square′
        (Equiv.trans (∘-resp-≈ʳ (F-resp-≈ ⊗ (Equiv.sym (identity ⊗) , Equiv.refl)))
                      assoc-commute-from)))
      where open MR Core

    perimeter‴ : [ ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ⇒ X ⊗₀ Y ⊗₀ unit  ]⟨
                   associator ⊗ᵢ ≅.refl                           ⇒⟨ (X ⊗₀ (Y ⊗₀ unit)) ⊗₀ unit ⟩
                   (associator                                    ⇒⟨ X ⊗₀ (Y ⊗₀ unit) ⊗₀ unit ⟩
                   ≅.refl ⊗ᵢ associator                           ⇒⟨ X ⊗₀ Y ⊗₀ unit ⊗₀ unit ⟩
                   ≅.refl ⊗ᵢ ≅.refl ⊗ᵢ unitorˡ)
                 ≈ ρu                                             ⇒⟨ (X ⊗₀ Y) ⊗₀ unit ⟩
                   associator
                 ⟩
    perimeter‴ = let α = associator in let λλ = unitorˡ in begin
      (≅.refl ⊗ᵢ ≅.refl ⊗ᵢ λλ ∘ᵢ ≅.refl ⊗ᵢ α ∘ᵢ α) ∘ᵢ α ⊗ᵢ ≅.refl  ≈⟨ assoc′ ⟩
       ≅.refl ⊗ᵢ ≅.refl ⊗ᵢ λλ ∘ᵢ (≅.refl ⊗ᵢ α ∘ᵢ α) ∘ᵢ α ⊗ᵢ ≅.refl ≈⟨ refl⟩∘⟨ assoc′ ⟩
       ≅.refl ⊗ᵢ ≅.refl ⊗ᵢ λλ ∘ᵢ ≅.refl ⊗ᵢ α ∘ᵢ α ∘ᵢ α ⊗ᵢ ≅.refl   ≈⟨ refl⟩∘⟨ pentagon-iso ⟩
       ≅.refl ⊗ᵢ ≅.refl ⊗ᵢ λλ ∘ᵢ α ∘ᵢ α                             ≈⟨ perimeter″ ⟩
       α ∘ᵢ ρu                                                       ∎

    top-face′ : [Xρ]u ∘ᵢ au ≃ ρu
    top-face′ = cut-squareʳ perimeter‴ (sym (glue◃◽′ tri′ (sym (lift-square′ assoc-commute-from))))
      where open MR Core
            tri′ : [ X ⊗₀ (Y ⊗₀ unit) ⊗₀ unit ⇒ X ⊗₀ Y ⊗₀ unit ]⟨
                   (≅.refl ⊗ᵢ ≅.refl ⊗ᵢ unitorˡ ∘ᵢ ≅.refl ⊗ᵢ associator)
                 ≈ ≅.refl ⊗ᵢ unitorʳ ⊗ᵢ ≅.refl
                 ⟩
            tri′ = lift-triangle′ ([ X ⊗- ]-resp-∘ triangle)

    coherence-iso₂ : [ (X ⊗₀ Y) ⊗₀ unit ⇒ X ⊗₀ Y ]⟨
                       ≅.refl ⊗ᵢ unitorʳ ∘ᵢ associator
                     ≈ unitorʳ
                     ⟩
    coherence-iso₂ = triangle-prism top-face′ square₁ square₂ (lift-square′ unitorʳ-commute-to)
      where square₁ : [ X ⊗₀ Y ⊗₀ unit ⇒ (X ⊗₀ Y) ⊗₀ unit ]⟨
                        ≅.sym unitorʳ ∘ᵢ ≅.refl ⊗ᵢ unitorʳ
                      ≈ (≅.refl ⊗ᵢ unitorʳ) ⊗ᵢ ≅.refl ∘ᵢ ≅.sym unitorʳ
                      ⟩
            square₁ = lift-square′ unitorʳ-commute-to

            square₂ : [ (X ⊗₀ Y) ⊗₀ unit ⇒ (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit ]⟨
                        ≅.sym unitorʳ ∘ᵢ associator
                      ≈ associator ⊗ᵢ ≅.refl ∘ᵢ ≅.sym unitorʳ
                      ⟩
            square₂ = lift-square′ unitorʳ-commute-to

    coherence₂ : C.id {X} ⊗₁ unitorʳ.from {Y} ∘ associator.from ≈ unitorʳ.from
    coherence₂ = project-triangle coherence-iso₂

  -- A third coherence condition (Lemma 2.3)

  coherence₃ : unitorˡ.from {unit} ≈ unitorʳ.from
  coherence₃ = push-eq unitorˡ-naturalIsomorphism (begin
      C.id ⊗₁ unitorˡ.from
    ≈˘⟨ cancelʳ associator.isoʳ ⟩
      (C.id ⊗₁ unitorˡ.from ∘ associator.from) ∘ associator.to
    ≈⟨ triangle ⟩∘⟨refl ⟩
      unitorʳ.from ⊗₁ C.id ∘ associator.to
    ≈⟨ unitor-coherenceʳ ⟩∘⟨refl ⟩
      unitorʳ.from ∘ associator.to
    ≈˘⟨ coherence₂ ⟩∘⟨refl ⟩
      (C.id ⊗₁ unitorʳ.from ∘ associator.from) ∘ associator.to
    ≈⟨ cancelʳ associator.isoʳ ⟩
      C.id ⊗₁ unitorʳ.from
    ∎)
    where
      open MR C hiding (push-eq)
      open C.HomReasoning

  coherence-iso₃ : [ unit ⊗₀ unit ⇒ unit ]⟨ unitorˡ ≈ unitorʳ ⟩
  coherence-iso₃ = ⌞ coherence₃ ⌟

open Kelly's using (coherence₁; coherence-iso₁; coherence₂; coherence-iso₂) public
