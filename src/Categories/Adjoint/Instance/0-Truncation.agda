{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Instance.0-Truncation where

-- The adjunction between 0-truncation and the inclusion functor from
-- Setoids to Categories/Groupoids.

open import Function.Base renaming (id to id→)
open import Function.Bundles using (Func)
import Function.Construct.Identity as Id
open import Relation.Binary using (Setoid)

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.Core using (Category)
open import Categories.Category.Construction.0-Groupoid using (0-Groupoid)
open import Categories.Category.Groupoid using (Groupoid)
open import Categories.Category.Instance.Groupoids using (Groupoids)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Instance.0-Truncation using (Trunc)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (refl)

-- The inclusion functor from Setoids to Groupoids

Inclusion : ∀ {c ℓ} e → Functor (Setoids c ℓ) (Groupoids c ℓ e)
Inclusion {c} {ℓ} e = record
  { F₀           = 0-Groupoid e
  ; F₁           = λ f → record { F₀ = to f; F₁ = cong f }
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ {S T f g} f≗g →
    let module S = Setoid S
        module T = Setoid T
    in record
    { F⇒G = record { η = λ _ → f≗g       }
    ; F⇐G = record { η = λ _ → T.sym f≗g }
    }
  }
  where open Func

-- Trunc is left-adjoint to the inclusion functor from Setoids to Groupoids

TruncAdj : ∀ {o ℓ e} → Trunc ⊣ Inclusion {o} {ℓ} e
TruncAdj {o} {ℓ} {e} = record
  { unit   = unit
  ; counit = counit
  ; zig    = λ {A} → Category.id (category A)
  ; zag    = refl
  }
  where
    open Func
    open Groupoid using (category)

    unit : NaturalTransformation idF (Inclusion e ∘F Trunc)
    unit = record
      { η           = λ _ → record { F₀ = id→ ; F₁ = id→ }
      ; commute     = λ _ → refl
      ; sym-commute = λ _ → refl
      }

    counit : NaturalTransformation (Trunc ∘F Inclusion e) idF
    counit = ntHelper record { η = Id.function; commute = λ {_} {Y} _ → Setoid.refl Y }
