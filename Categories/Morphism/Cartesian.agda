{-# OPTIONS --without-K --safe #-}

module Categories.Morphism.Cartesian where

open import Level

open import Categories.Category
open import Categories.Functor

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

record Cartesian (F : Functor C D) {X Y} (f : C [ X , Y ]) : Set (levelOfTerm F) where
  private
    module C = Category C
    module D = Category D
    open Functor F
    open D

  field
    universal : ∀ {A} {u : F₀ A ⇒ F₀ X} (h : C [ A , Y ]) →
                  F₁ f ∘ u ≈ F₁ h →  C [ A , X ]
    commute   : ∀ {A} {u : F₀ A ⇒ F₀ X} {h : C [ A , Y ]}
                  (eq : F₁ f ∘ u ≈ F₁ h) →
                  C [ C [ f ∘ universal h eq ] ≈ h ]
    compat    : ∀ {A} {u : F₀ A ⇒ F₀ X} {h : C [ A , Y ]}
                  (eq : F₁ f ∘ u ≈ F₁ h) →
                  F₁ (universal h eq) ≈ u
