{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Instance.01-Truncation where

-- The adjunction between (0,1)-truncation and the inclusion functor
-- from Posets to Categories.

open import Data.Product using (_,_)
import Function
open import Relation.Binary using (Poset)
open import Relation.Binary.OrderMorphism using (_⇒-Poset_)

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.Construction.Thin using (Thin)
open import Categories.Category using (Category)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Posets using (Posets)
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Instance.01-Truncation using (Trunc)
open import Categories.NaturalTransformation
  using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (refl)

open _⇒-Poset_

-- The inclusion functor from Posets to Categories

Inclusion : ∀ {c ℓ₁ ℓ₂} e → Functor (Posets c ℓ₁ ℓ₂) (Cats c ℓ₂ e)
Inclusion {c} {ℓ₁} e = record
  { F₀           = Thin e
  ; F₁           = λ f → record { F₀ = fun f ; F₁ = monotone f }
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ {A B f g} f≗g →
    let open Poset B
    in record
    { F⇒G = record { η = λ _ → reflexive f≗g          }
    ; F⇐G = record { η = λ _ → reflexive (Eq.sym f≗g) }
    }
  }

-- Trunc is left-adjoint to the inclusion functor from Setoids to Groupoids

TruncAdj : ∀ {o ℓ e} → Trunc ⊣ Inclusion {o} {ℓ} e
TruncAdj {o} {ℓ} {e} = record
  { unit   = unit
  ; counit = counit
  ; zig    = λ {C} → id C , id C
  ; zag    = refl
  }
  where
    open Category

    unit : NaturalTransformation idF (Inclusion e ∘F Trunc)
    unit = record
      { η           = λ _ → record { F₀ = Function.id ; F₁ = Function.id }
      ; commute     = λ _ → refl
      ; sym-commute = λ _ → refl
      }

    counit : NaturalTransformation (Trunc ∘F Inclusion e) idF
    counit = ntHelper record
      { η       = λ _ → record { fun = Function.id ; monotone = Function.id }
      ; commute = λ {_ D} _ → Poset.Eq.refl D
      }
