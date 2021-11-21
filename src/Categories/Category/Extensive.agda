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
  open Cocartesian

  field
    cocartesian : Cocartesian 𝒞
    pullback-of-inl : {A B C : Obj} (f : A ⇒ _+_ cocartesian B C) → Pullback 𝒞 f (i₁ cocartesian)
    pullback-of-inr : {A B C : Obj} (f : A ⇒ _+_ cocartesian B C) → Pullback 𝒞 f (i₂ cocartesian)
    pullback-of-cp-is-cp : {A B C : Obj} (f : A ⇒ _+_ cocartesian B C) → IsCoproduct 𝒞 (p₁ (pullback-of-inl f)) (p₁ (pullback-of-inr f))
    
    inl-is-mono : ∀ {A B : Obj} → Mono 𝒞 (i₁ cocartesian {A = A}{B = B})
    inr-is-mono : ∀ {A B : Obj} → Mono 𝒞 (i₂ cocartesian {A = A}{B = B})

    disjoint : ∀ {A B : Obj} → IsPullback 𝒞 (¡ cocartesian) (¡ cocartesian) (i₁ cocartesian {A = A}{B = B}) (i₂ cocartesian {A = A}{B = B})











