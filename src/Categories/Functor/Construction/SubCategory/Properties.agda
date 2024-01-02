{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Construction.SubCategory.Properties {o ℓ e} (C : Category o ℓ e) where

open Category C
open Equiv

open import Data.Product using (_,_)
open import Level
open import Function.Base    using () renaming (id to id→)
open import Function.Bundles using (Surjection)

open import Categories.Category.SubCategory C
open import Categories.Functor.Construction.SubCategory C
open import Categories.Functor.Properties

private
  variable
    ℓ′ i : Level
    I : Set i
    U : I → Obj

SubFaithful : ∀ (sub : SubCat {i} {ℓ′} I) → Faithful (Sub sub)
SubFaithful _ x≈y = x≈y

FullSubFaithful : Faithful (FullSub {U = U})
FullSubFaithful = id→

FullSubFull : Full (FullSub {U = U})
FullSubFull f = f , refl
