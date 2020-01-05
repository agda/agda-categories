{-# OPTIONS --without-K --safe #-}
module Categories.Comonad where

open import Level

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)
open import Categories.NaturalTransformation.Equivalence
open NaturalIsomorphism

record Comonad {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : Endofunctor C
    ε : NaturalTransformation F idF
    δ : NaturalTransformation F (F ∘F F)

  module F = Functor F
  module ε = NaturalTransformation ε
  module δ = NaturalTransformation δ

  open Category C
  open Functor F

  field
    assoc     : ∀ {X : Obj} → δ.η (F₀ X) ∘ δ.η X ≈ F₁ (δ.η X) ∘ δ.η X
    sym-assoc : ∀ {X : Obj} → F₁ (δ.η X) ∘ δ.η X ≈ δ.η (F₀ X) ∘ δ.η X
    identityˡ : ∀ {X : Obj} → F₁ (ε.η X) ∘ δ.η X ≈ id
    identityʳ : ∀ {X : Obj} → ε.η (F₀ X) ∘ δ.η X ≈ id
