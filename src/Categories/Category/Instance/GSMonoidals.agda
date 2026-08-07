{-# OPTIONS --without-K --safe #-}

-- The categories of gs-monoidal categories, with lax and with strong
-- gs-monoidal functors as morphisms, and symmetric monoidal natural
-- isomorphism as equality of morphisms.
--
-- A gs-monoidal natural transformation is a monoidal one and nothing more:
-- neither comonoid map is natural, so there is no further square to respect.
-- StrongGSMonoidals is therefore the 2-category gsCat of the literature,
-- whose 1-cells are the strong functors, and GSMonoidals is its lax variant.

module Categories.Category.Instance.GSMonoidals where

open import Level

open import Relation.Binary using (IsEquivalence)

open import Categories.Category.Core using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Monoidal.GSMonoidal.Bundle using (GSMonoidalCategory)

import Categories.Functor.Monoidal.GSMonoidal as GSMF
open import Categories.Functor.Monoidal.GSMonoidal.Properties
  using (idF-GSMonoidal; ∘-GSMonoidal; idF-StrongGSMonoidal; ∘-StrongGSMonoidal)
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric as SMNI

module _ o ℓ e where

  GSMonoidals : Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
  GSMonoidals = categoryHelper record
    { Obj       = GSMonoidalCategory o ℓ e
    ; _⇒_       = GSMF.Lax.GSMonoidalFunctor
    ; _≈_       = λ F G → SMF F ≃ SMF G
    ; id        = idF-GSMonoidal _
    ; _∘_       = ∘-GSMonoidal
    -- NOTE: as in Categories.Category.Instance.Monoidals, the η-expanded
    -- versions typecheck much faster.
    ; assoc     = λ {_ _ _ _ F G H} → associator {F = SMF F} {SMF G} {SMF H}
    ; identityˡ = λ {_ _ F} → unitorˡ {F = SMF F}
    ; identityʳ = λ {_ _ F} → unitorʳ {F = SMF F}
    ; equiv     = record
      { refl  = IsEquivalence.refl  isEquivalence
      ; sym   = IsEquivalence.sym   isEquivalence
      ; trans = IsEquivalence.trans isEquivalence
      }
    ; ∘-resp-≈  = _ⓘₕ_
    }
    where
      open SMNI.Lax
      open GSMF.Lax.GSMonoidalFunctor using ()
        renaming (symmetricMonoidalFunctor to SMF)

  StrongGSMonoidals : Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
  StrongGSMonoidals = categoryHelper record
    { Obj       = GSMonoidalCategory o ℓ e
    ; _⇒_       = GSMF.Strong.GSMonoidalFunctor
    ; _≈_       = λ F G → SMF F ≃ SMF G
    ; id        = idF-StrongGSMonoidal _
    ; _∘_       = ∘-StrongGSMonoidal
    ; assoc     = λ {_ _ _ _ F G H} → associator {F = SMF F} {SMF G} {SMF H}
    ; identityˡ = λ {_ _ F} → unitorˡ {F = SMF F}
    ; identityʳ = λ {_ _ F} → unitorʳ {F = SMF F}
    ; equiv     = record
      { refl  = IsEquivalence.refl  isEquivalence
      ; sym   = IsEquivalence.sym   isEquivalence
      ; trans = IsEquivalence.trans isEquivalence
      }
    ; ∘-resp-≈  = _ⓘₕ_
    }
    where
      open SMNI.Strong
      open GSMF.Strong.GSMonoidalFunctor using ()
        renaming (symmetricMonoidalFunctor to SMF)
