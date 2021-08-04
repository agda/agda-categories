{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

module Categories.Category.Construction.MonoidalFunctors {o ℓ e o′ ℓ′ e′}
  (C : MonoidalCategory o ℓ e) (D : MonoidalCategory o′ ℓ′ e′) where

-- The functor category for a given pair of monoidal categories

open import Level
open import Data.Product using (_,_)
open import Relation.Binary.Construct.On using (isEquivalence)
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Functor.Monoidal
import Categories.NaturalTransformation.Monoidal as NT
open import Categories.NaturalTransformation.Equivalence
  using (_≃_; ≃-isEquivalence)

open MonoidalCategory D

module Lax where

  MonoidalFunctors : Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′)
                              (o ⊔ e′)
  MonoidalFunctors = record
    { Obj = MonoidalFunctor C D
    ; _⇒_ = MonoidalNaturalTransformation
    ; _≈_ = λ α β → U α ≃ U β
    ; id  = idNT
    ; _∘_ = _∘ᵥ_
    ; assoc     = assoc
    ; sym-assoc = sym-assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = identity²
    ; equiv     = isEquivalence U ≃-isEquivalence
    ; ∘-resp-≈  = λ α₁≈β₁ α₂≈β₂ → ∘-resp-≈ α₁≈β₁ α₂≈β₂
    }
    where
      open NT.Lax renaming (id to idNT)
      open MonoidalNaturalTransformation using (U)

module Strong where

  MonoidalFunctors : Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′)
                              (o ⊔ e′)
  MonoidalFunctors = record
    { Obj = StrongMonoidalFunctor C D
    ; _⇒_ = MonoidalNaturalTransformation
    ; _≈_ = λ α β → U α ≃ U β
    ; id  = idNT
    ; _∘_ = _∘ᵥ_
    ; assoc     = assoc
    ; sym-assoc = sym-assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = identity²
    ; equiv     = isEquivalence U ≃-isEquivalence
    ; ∘-resp-≈  = λ α₁≈β₁ α₂≈β₂ → ∘-resp-≈ α₁≈β₁ α₂≈β₂
    }
    where
      open NT.Strong renaming (id to idNT)
      open MonoidalNaturalTransformation using (U)
