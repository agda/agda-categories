{-# OPTIONS --without-K --safe #-}
module Categories.Monad where

open import Level

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)
open import Categories.NaturalTransformation.Equivalence
open NaturalIsomorphism

record Monad {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : Endofunctor C
    η : NaturalTransformation idF F
    μ : NaturalTransformation (F ∘F F) F

  module F = Functor F
  module η = NaturalTransformation η
  module μ = NaturalTransformation μ

  open Category C
  open F

  field
    assoc     : ∀ {X : Obj} → μ.η X ∘ F₁ (μ.η X) ≈ μ.η X ∘ μ.η (F₀ X)
    sym-assoc : ∀ {X : Obj} → μ.η X ∘ μ.η (F₀ X) ≈ μ.η X ∘ F₁ (μ.η X)
    identityˡ : ∀ {X : Obj} → μ.η X ∘ F₁ (η.η X) ≈ id
    identityʳ : ∀ {X : Obj} → μ.η X ∘ η.η (F₀ X) ≈ id
