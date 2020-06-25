{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Representable where

-- A Presheaf (into Setoids) is representation if it is naturally isomorphic to a Hom functor
--  over a particular object A of the base category.
open import Level

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids
open import Categories.Functor using (Functor)
open import Categories.Functor.Hom
open import Categories.Functor.Presheaf
open import Categories.NaturalTransformation.NaturalIsomorphism

record Representable {o ℓ e} {C : Category o ℓ e} (F : Presheaf C (Setoids ℓ e)) : Set (o ⊔ suc ℓ ⊔ suc e) where
  open Category C
  open Hom C
  field
    A : Obj
    Iso : NaturalIsomorphism F Hom[-, A ]
