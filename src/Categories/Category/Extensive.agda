{-# OPTIONS --without-K --safe #-}

module Categories.Category.Extensive where

-- https://ncatlab.org/nlab/show/extensive+category

open import Level

open import Categories.Category.Core
open import Categories.Diagram.Pullback
open import Categories.Category.Cocartesian
open import Categories.Object.Coproduct
open import Categories.Morphism

record Extensive {o ℓ e : Level} (𝒞 : Category o ℓ e) : Set (suc (o ⊔ ℓ ⊔ e)) where
  open Category 𝒞
  open Pullback

  field
    cocartesian : Cocartesian 𝒞

  module CC = Cocartesian cocartesian
  open CC using (_+_; i₁; i₂; ¡)

  field
    pullback₁ : {A B C : Obj} (f : A ⇒ B + C) → Pullback 𝒞 f i₁
    pullback₂ : {A B C : Obj} (f : A ⇒ B + C) → Pullback 𝒞 f i₂
    pullback-of-cp-is-cp : {A B C : Obj} (f : A ⇒ B + C) → IsCoproduct 𝒞 (p₁ (pullback₁ f)) (p₁ (pullback₂ f))
    
    pullback₁-is-mono : ∀ {A B : Obj} → Mono 𝒞 (i₁ {A = A}{B = B})
    pullback₂-is-mono : ∀ {A B : Obj} → Mono 𝒞 (i₂ {A = A}{B = B})

    disjoint : ∀ {A B : Obj} → IsPullback 𝒞 ¡ ¡ (i₁ {A = A}{B = B}) i₂











