{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Experiments.Category.PreAbelian {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Category.Additive

open import Categories.Object.Kernel
open import Categories.Object.Cokernel

open Category 𝒞
open HomReasoning

private
  variable
    A B C : Obj
    f g : A ⇒ B

record PreAbelian : Set (o ⊔ ℓ ⊔ e) where
  field
    additive : Additive 𝒞 

  open Additive additive public

  field
    kernel   : (f : A ⇒ B) → Kernel 𝟎 f
    cokernel : (f : A ⇒ B) → Cokernel 𝟎 f

