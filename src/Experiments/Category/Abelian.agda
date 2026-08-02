{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Experiments.Category.Abelian {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Data.Product using (Σ-syntax; _,_)

open import Experiments.Category.Additive
open import Experiments.Category.PreAbelian

open import Categories.Object.Zero
open import Categories.Object.Kernel
open import Categories.Object.Cokernel

open import Categories.Morphism 𝒞
open import Categories.Morphism.Normal 𝒞

open Category 𝒞
open HomReasoning

private
  variable
    A B C : Obj
    f g k : A ⇒ B

record Abelian : Set (o ⊔ ℓ ⊔ e) where
  field
     preAbelian : PreAbelian 𝒞

  open PreAbelian preAbelian public

  field
    mono-is-normal : ∀ {A K} {k : K ⇒ A} → Mono k → IsNormalMonomorphism 𝟎 k
    epi-is-normal  : ∀ {B K} {k : B ⇒ K} → Epi k → IsNormalEpimorphism 𝟎 k
