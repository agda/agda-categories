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
    o ℓ e o′ ℓ′  : Level

record Concrete : Set (suc (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′)) where
  field
    cat : Category o ℓ e
    concretize : Functor cat (Setoids o′ ℓ′)
    conc-faithful : Faithful concretize

record RepresentablyConcrete : Set (suc (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′)) where
  open Concrete
  field
    conc : Concrete {o} {ℓ} {e}
    representable : Representable (concretize conc)
