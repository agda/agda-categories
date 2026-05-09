{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Preadditive

module Experiments.Category.Additive {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Object.Biproduct 𝒞
open import Categories.Object.Zero 𝒞

open Category 𝒞

record Additive : Set (o ⊔ ℓ ⊔ e) where

  infixr 7 _⊕_

  field
    preadditive : Preadditive 𝒞
    𝟎 : Zero
    biproduct : ∀ {A B} → Biproduct A B

  open Preadditive preadditive public

  open Zero 𝟎 public
  module biproduct {A} {B} = Biproduct (biproduct {A} {B})

  _⊕_ : Obj → Obj → Obj
  A ⊕ B = Biproduct.A⊕B (biproduct {A} {B})

  open biproduct public
