{-# OPTIONS --without-K --safe #-}

module Categories.Category.Regular where

-- https://ncatlab.org/nlab/show/regular+category
-- https://en.wikipedia.org/wiki/Regular_category

open import Level

open import Categories.Category.Core
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Diagram.Coequalizer
open import Categories.Diagram.KernelPair
open import Categories.Diagram.Pullback
open import Categories.Morphism.Regular

record Regular {o ℓ e : Level} (𝒞 : Category o ℓ e) : Set (suc (o ⊔ ℓ ⊔ e)) where
  open Category 𝒞

  open Pullback

  field
    finitely-complete : FinitelyComplete 𝒞
    coeq-of-kernelpairs : {A B : Obj} (f : A ⇒ B) (kp : KernelPair 𝒞 f) → Coequalizer 𝒞 (p₁ kp) (p₂ kp)
    pullback-of-regularepi-is-regularepi : {A B C : Obj} (f : B ⇒ A) {g : C ⇒ A} (p : Pullback 𝒞 f g) → RegularEpi 𝒞 (p₂ p)
