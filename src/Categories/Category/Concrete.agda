{-# OPTIONS --without-K --safe #-}

module Categories.Category.Concrete where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Representable using (Representable)
open import Categories.Functor.Properties using (Faithful)

-- A Concrete Category is a category along with a faithful
-- functor to Setoid.
-- [Normally Set, but that doesn't work so well here]

private
  variable
    o ℓ e : Level

record Concrete (C : Category o ℓ e) (ℓ′ e′ : Level) : Set (o ⊔ ℓ ⊔ e ⊔ suc (ℓ′ ⊔ e′)) where
  field
    concretize : Functor C (Setoids ℓ′ e′)
    conc-faithful : Faithful concretize

-- Because of the use of the Hom functor, some levels collapse
record RepresentablyConcrete (C : Category o ℓ e) : Set (o ⊔ suc (e ⊔ ℓ)) where
  open Concrete
  field
    conc : Concrete C ℓ e
    representable : Representable (concretize conc)
