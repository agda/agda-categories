{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Monoidals where

open import Level

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism

module _ o ℓ e where

  Monoidals : Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
  Monoidals = categoryHelper record
    { Obj       = MonoidalCategory o ℓ e
    ; _⇒_       = MonoidalFunctor
    ; _≈_       = λ F G → M.F F ≃ M.F G
    ; id        = idF-Monoidal _
    ; _∘_       = ∘-Monoidal
    ; assoc     = λ {_ _ _ _ F G H} → associator (M.F F) (M.F G) (M.F H)
    ; identityˡ = unitorˡ
    ; identityʳ = unitorʳ
    ; equiv     = record
      { refl  = ≃.refl
      ; sym   = ≃.sym
      ; trans = ≃.trans
      }
    ; ∘-resp-≈  = _ⓘₕ_
    }
    where module M = MonoidalFunctor

  StrongMonoidals : Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
  StrongMonoidals = categoryHelper record
    { Obj       = MonoidalCategory o ℓ e
    ; _⇒_       = StrongMonoidalFunctor
    ; _≈_       = λ F G → M.F F ≃ M.F G
    ; id        = idF-StrongMonoidal _
    ; _∘_       = ∘-StrongMonoidal
    ; assoc     = λ {_ _ _ _ F G H} → associator (M.F F) (M.F G) (M.F H)
    ; identityˡ = unitorˡ
    ; identityʳ = unitorʳ
    ; equiv     = record
      { refl  = ≃.refl
      ; sym   = ≃.sym
      ; trans = ≃.trans
      }
    ; ∘-resp-≈  = _ⓘₕ_
    }
    where module M = StrongMonoidalFunctor
