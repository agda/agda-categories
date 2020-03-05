{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Instance.StrictCore where

-- The adjunction between the forgetful functor from (strict) Cats to
-- (strict) Groupoids and the (strict) Core functor.

open import Data.Product
open import Level using (_⊔_)
import Function
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Adjoint
open import Categories.Category using (Category)
open import Categories.Category.Groupoid using (Groupoid)
import Categories.Category.Construction.Core as C
open import Categories.Category.Instance.StrictCats
open import Categories.Category.Instance.StrictGroupoids
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Equivalence
open import Categories.Functor.Instance.StrictCore
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MR
open import Categories.Morphism.IsoEquiv using (⌞_⌟; _≃_)

-- The forgetful functor from StrictGroupoids to StrictCats

Forgetful : ∀ {o ℓ e} → Functor (Groupoids o ℓ e) (Cats o ℓ e)
Forgetful {o} {ℓ} {e} = record
  { F₀ = Groupoid.category
  ; F₁ = Function.id
  ; identity     = λ {G} → Groupoids.Equiv.refl {G} {G} {idF}
  ; homomorphism = λ {G H K F H} → Groupoids.Equiv.refl {G} {K} {H ∘F F}
  ; F-resp-≈     = Function.id
  }
  where
    module Groupoids = Category (Groupoids o ℓ e)

-- Core is right-adjoint to the forgetful functor from Groupoids to
-- Cats

CoreAdj : ∀ {o ℓ e} → Forgetful {o} {ℓ ⊔ e} {e} ⊣ Core
CoreAdj = record
  { unit   = record { η = unit   ; commute = λ {G H} F → unit-commute {G} {H} F ; sym-commute = λ {G H} F → unit-sym-commute {G} {H} F }
  ; counit = record { η = counit ; commute = counit-commute                     ; sym-commute = counit-sym-commute }
  ; zig    = λ {G} → zig {G}
  ; zag    = zag
  }
  where
    open Groupoid using (category)
    module Core = Functor Core

    unit : ∀ G → Functor (category G) (C.Core (category G))
    unit G = record
      { F₀ = Function.id
      ; F₁ = λ f → record { from = f ; to = f ⁻¹ ; iso = iso }
      ; identity     = ⌞ Equiv.refl ⌟
      ; homomorphism = ⌞ Equiv.refl ⌟
      ; F-resp-≈     = ⌞_⌟
      }
      where open Groupoid G

    unit-commute : ∀ {G H} (F : Functor (category G) (category H)) →
                   unit H ∘F F ≡F Core.F₁ F ∘F unit G
    unit-commute {_} {H} F = record
      { eq₀ = λ _ → refl
      ; eq₁ = λ _ → ⌞ MR.id-comm-sym (category H) ⌟
      }

    unit-sym-commute : ∀ {G H} (F : Functor (category G) (category H)) →
                       Core.F₁ F ∘F unit G ≡F unit H ∘F F
    unit-sym-commute {_} {H} F = record
      { eq₀ = λ _ → refl
      ; eq₁ = λ _ → ⌞ MR.id-comm-sym (category H) ⌟
      }

    counit : ∀ C → Functor (C.Core C) C
    counit C = record
      { F₀ = Function.id
      ; F₁ = _≅_.from
      ; identity     = Equiv.refl
      ; homomorphism = Equiv.refl
      ; F-resp-≈     = _≃_.from-≈
      }
      where
        open Category C
        open Morphism C

    counit-commute : ∀ {C D} (F : Functor C D) →
                     counit D ∘F Core.F₁ F ≡F F ∘F counit C
    counit-commute {C} {D} F = record
      { eq₀ = λ _ → refl
      ; eq₁ = λ _ → MR.id-comm-sym D
      }
      
    counit-sym-commute : ∀ {C D} (F : Functor C D) →
                         F ∘F counit C ≡F counit D ∘F Core.F₁ F
    counit-sym-commute {C} {D} F = record
      { eq₀ = λ _ → refl
      ; eq₁ = λ _ → MR.id-comm-sym D
      }

    zig : ∀ {G} → counit (category G) ∘F unit G ≡F idF
    zig {G} = record
      { eq₀ = λ _ → refl
      ; eq₁ = λ _ → MR.id-comm-sym (category G)
      }

    zag : ∀ {B} → Core.F₁ (counit B) ∘F unit (Core.F₀ B) ≡F idF
    zag {B} = record { eq₀ = λ _ → refl ; eq₁ = λ _ → ⌞ MR.id-comm-sym B ⌟ }
