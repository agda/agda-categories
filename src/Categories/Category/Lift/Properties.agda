{-# OPTIONS --without-K --safe #-}

module Categories.Category.Lift.Properties where

open import Level

open import Categories.Category.Core
open import Categories.Category.Equivalence
open import Categories.Category.Lift
open import Categories.NaturalTransformation.NaturalIsomorphism
import Categories.Morphism.Reasoning.Core as MR

unliftF-liftF-weakInverse : ∀ {o ℓ e} o′ ℓ′ e′ (C : Category o ℓ e) → WeakInverse (unliftF o′ ℓ′ e′ C) (liftF o′ ℓ′ e′ C)
unliftF-liftF-weakInverse o′ ℓ′ e′ C = record
  { F∘G≈id = niHelper record
    { η = λ X → id
    ; η⁻¹ = λ X → id
    ; commute = λ f → id-comm-sym
    ; iso = λ X → record
      { isoˡ = identity²
      ; isoʳ = identity²
      }
    }
  ; G∘F≈id = niHelper record
    { η = λ X → lift id
    ; η⁻¹ = λ X → lift id
    ; commute = λ f → lift id-comm-sym
    ; iso = λ X → record
      { isoˡ = lift identity²
      ; isoʳ = lift identity²
      }
    }
  }
  where
    open Category C
    open MR C

liftC-strongEquivalence : ∀ {o ℓ e} o′ ℓ′ e′ (C : Category o ℓ e) → StrongEquivalence (liftC o′ ℓ′ e′ C) C
liftC-strongEquivalence o′ ℓ′ e′ C = record { weak-inverse = unliftF-liftF-weakInverse o′ ℓ′ e′ C }
