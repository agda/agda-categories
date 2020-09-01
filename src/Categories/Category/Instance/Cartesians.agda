{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Cartesians where

open import Level

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Cartesian.Structure
open import Categories.Functor.Cartesian
open import Categories.Functor.Cartesian.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism

module _ o ℓ e where

  Cartesians : Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
  Cartesians = categoryHelper record
    { Obj       = CartesianCategory o ℓ e
    ; _⇒_       = CartesianF
    ; _≈_       = λ F G → CF.F F ≃ CF.F G
    ; id        = idF-CartesianF _
    ; _∘_       = ∘-CartesianF
    ; assoc     = λ {_ _ _ _ F G H} → associator (CF.F F) (CF.F G) (CF.F H)
    ; identityˡ = unitorˡ
    ; identityʳ = unitorʳ
    ; equiv     = record
      { refl  = ≃.refl
      ; sym   = ≃.sym
      ; trans = ≃.trans
      }
    ; ∘-resp-≈  = _ⓘₕ_
    }
    where module CF = CartesianF
