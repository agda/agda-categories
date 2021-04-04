{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Construction.SubCategory {o ℓ e} (C : Category o ℓ e) where

open import Categories.Category.SubCategory C

open Category C
open Equiv

open import Level
open import Function.Base using () renaming (id to id→)
open import Data.Product

open import Categories.Functor using (Functor)

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

FullSub : Functor (FullSubCategory U) C
FullSub {U = U} = record
  { F₀ = U
  ; F₁ = id→
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = id→
  }
