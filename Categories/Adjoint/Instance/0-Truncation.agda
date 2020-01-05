{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Instance.0-Truncation where

-- The adjunction between 0-truncation and the inclusion functor from
-- Setoids to Categories/Groupoids.

open import Level using (Lift)
open import Data.Unit using (⊤)
import Function
open import Relation.Binary using (Setoid)
open import Function.Equality using (Π) renaming (id to idΠ)

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.Construction.0-Groupoid using (0-Groupoid)
open import Categories.Category.Groupoid using (Groupoid)
open import Categories.Category.Instance.Groupoids using (Groupoids)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Instance.0-Truncation using (Trunc)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (refl)

-- The inclusion functor from Setoids to Groupoids

Inclusion : ∀ {c ℓ} e → Functor (Setoids c ℓ) (Groupoids c ℓ e)
Inclusion {c} {ℓ} e = record
  { F₀           = 0-Groupoid e
  ; F₁           = λ f → record { F₀ = f ⟨$⟩_ ; F₁ = cong f }
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ {S T f g} f≗g →
    let module S = Setoid S
        module T = Setoid T
    in record
    { F⇒G = record { η = λ _ → f≗g S.refl         }
    ; F⇐G = record { η = λ _ → T.sym (f≗g S.refl) }
    }
  }
  where open Π

-- Trunc is left-adjoint to the inclusion functor from Setoids to Groupoids

TruncAdj : ∀ {o ℓ e} → Trunc ⊣ Inclusion {o} {ℓ} e
TruncAdj {o} {ℓ} {e} = record
  { unit   = unit
  ; counit = counit
  ; zig    = Function.id
  ; zag    = refl
  }
  where
    open Π
    open Groupoid using (category)

    unit : NaturalTransformation idF (Inclusion e ∘F Trunc)
    unit = record
      { η           = λ _ → record { F₀ = Function.id ; F₁ = Function.id }
      ; commute     = λ _ → refl
      ; sym-commute = λ _ → refl
      }

    counit : NaturalTransformation (Trunc ∘F Inclusion e) idF
    counit = ntHelper record { η = λ S → idΠ ; commute = λ f → cong f }
