{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Monoidals where

open import Level

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal

module _ o ℓ e where

  Monoidals : Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
  Monoidals = categoryHelper record
    { Obj       = MonoidalCategory o ℓ e
    ; _⇒_       = MonoidalFunctor
    ; _≈_       = Lax._≃_
    ; id        = idF-Monoidal _
    ; _∘_       = ∘-Monoidal
    -- NOTE: these η-expanded versions typecheck much faster...
    ; assoc     = λ {_ _ _ _ F G H} → associator {F = F} {G} {H}
    ; identityˡ = λ {_ _ F} → unitorˡ {F = F}
    ; identityʳ = λ {_ _ F} → unitorʳ {F = F}
    ; equiv     = isEquivalence
    ; ∘-resp-≈  = _ⓘₕ_
    }
    where open Lax

  StrongMonoidals : Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
  StrongMonoidals = categoryHelper record
    { Obj       = MonoidalCategory o ℓ e
    ; _⇒_       = StrongMonoidalFunctor
    ; _≈_       = Strong._≃_
    ; id        = idF-StrongMonoidal _
    ; _∘_       = ∘-StrongMonoidal
    -- NOTE: these η-expanded versions typecheck much faster...
    ; assoc     = λ {_ _ _ _ F G H} → associator {F = F} {G} {H}
    ; identityˡ = λ {_ _ F} → unitorˡ {F = F}
    ; identityʳ = λ {_ _ F} → unitorʳ {F = F}
    ; equiv     = isEquivalence
    ; ∘-resp-≈  = _ⓘₕ_
    }
    where open Strong
