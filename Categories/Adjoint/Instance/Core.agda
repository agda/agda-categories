{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Instance.Core where

-- The adjunction between the forgetful functor from Cats to Groupoids
-- and the Core functor.

open import Level using (_⊔_)
import Function

open import Categories.Adjoint using (_⊣_)
open import Categories.Category using (Category)
import Categories.Category.Construction.Core as C
open import Categories.Category.Groupoid using (Groupoid)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Groupoids using (Groupoids)
open import Categories.Functor using (Functor; _∘F_; id)
open import Categories.Functor.Instance.Core using (Core)
import Categories.Morphism as Morphism
open import Categories.Morphism.IsoEquiv using (⌞_⌟)
open import Categories.NaturalTransformation.NaturalIsomorphism using (refl; _≃_)

-- The forgetful functor from Groupoids to Cats

Forgetful : ∀ {o ℓ e} → Functor (Groupoids o ℓ e) (Cats o ℓ e)
Forgetful = record
  { F₀ = category
  ; F₁ = Function.id
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = Function.id
  }
  where open Groupoid

-- Core is right-adjoint to the forgetful functor from Groupoids to
-- Cats

CoreAdj : ∀ {o ℓ e} → Forgetful {o} {ℓ ⊔ e} {e} ⊣ Core
CoreAdj = record
  { unit   = record { η = unit   ; commute = λ {G} {H} F → unit-commute {G} {H} F }
  ; counit = record { η = counit ; commute = counit-commute }
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
      ; F-resp-≈     = λ eq → ⌞ eq ⌟
      }
      where open Groupoid G

    unit-commute : ∀ {G H} (F : Functor (category G) (category H)) →
                   unit H ∘F F ≃ Core.F₁ F ∘F unit G
    unit-commute {G} {H} F = record
      { F⇒G = record { η = λ _ → ≅.refl  ; commute = λ _ → ⌞ Equiv.sym id-comm ⌟ }
      ; F⇐G = record { η = λ _ → ≅.refl  ; commute = λ _ → ⌞ Equiv.sym id-comm ⌟ }
      ; iso = λ _ → record { isoˡ = ⌞ identityˡ ⌟ ; isoʳ = ⌞ identityˡ ⌟ }
      }
      where
        open Groupoid H
        open Morphism (category H)

    counit : ∀ C → Functor (C.Core C) C
    counit C = record
      { F₀ = Function.id
      ; F₁ = _≅_.from
      ; identity     = Equiv.refl
      ; homomorphism = Equiv.refl
      ; F-resp-≈     = λ where ⌞ eq ⌟ → eq
      }
      where
        open Category C
        open Morphism C

    counit-commute : ∀ {C D} (F : Functor C D) →
                     counit D ∘F Core.F₁ F ≃ F ∘F counit C
    counit-commute {C} {D} F = record
      { F⇒G = record { η = λ _ → D.id  ; commute = λ _ → D.Equiv.sym D.id-comm }
      ; F⇐G = record { η = λ _ → D.id  ; commute = λ _ → D.Equiv.sym D.id-comm }
      ; iso = λ _ → _≅_.iso ≅.refl
      }
      where
        module D = Category D
        open Morphism D

    zig : ∀ {G} → counit (category G) ∘F unit G ≃ id
    zig {G} = record
      { F⇒G = record { η = λ _ → G.id ; commute = λ _ → G.Equiv.sym G.id-comm }
      ; F⇐G = record { η = λ _ → G.id ; commute = λ _ → G.Equiv.sym G.id-comm }
      ; iso = λ _ → _≅_.iso ≅.refl
      }
      where
        module G = Groupoid G
        open Morphism G.category

    zag : ∀ {B} → Core.F₁ (counit B) ∘F unit (Core.F₀ B) ≃ id
    zag {B} = record
      { F⇒G = record { η = λ _ → ≅.refl ; commute = λ _ → ⌞ Equiv.sym id-comm ⌟ }
      ; F⇐G = record { η = λ _ → ≅.refl ; commute = λ _ → ⌞ Equiv.sym id-comm ⌟ }
      ; iso = λ _ → record { isoˡ = ⌞ identityˡ ⌟ ; isoʳ = ⌞ identityˡ ⌟ }
      }
      where
        open Category B
        open Morphism B
