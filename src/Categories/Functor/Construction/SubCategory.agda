{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Construction.SubCategory {o ℓ e} (C : Category o ℓ e) where

open import Categories.Category.SubCategory C

open Category C
open Equiv

open import Level
open import Data.Product

open import Function.Base       using () renaming (id to id→)
open import Function.Surjection using (Surjection) renaming (id to id↠)

open import Categories.Functor using (Functor)
open import Categories.Functor.Properties

private
  variable
    ℓ′ i : Level
    I : Set i
    U : I → Obj

Sub : ∀ (sub : SubCat {i} {ℓ′} I) → Functor (SubCategory sub) C
Sub (record {U = U}) = record
  { F₀ = U
  ; F₁ = proj₁
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = id→
  }

SubFaithful : ∀ (sub : SubCat {i} {ℓ′} I) → Faithful (Sub sub)
SubFaithful _ _ _ = id→

FullSub : Functor (FullSubCategory U) C
FullSub {U = U} = record
  { F₀ = U
  ; F₁ = id→
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = id→
  }

FullSubFaithful : Faithful (FullSub {U = U})
FullSubFaithful _ _ = id→

FullSubFull : Full (FullSub {U = U})
FullSubFull = Surjection.surjective id↠
