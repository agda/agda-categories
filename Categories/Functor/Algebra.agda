{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Algebra where

-- Algebra for a Functor

open import Level
open import Function using (_$_)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor)

record F-Algebra {o ℓ e} {C : Category o ℓ e} (F : Endofunctor C) : Set (o ⊔ ℓ) where
  open Category C
  field
    A : Obj
    α : Functor.F₀ F A ⇒ A

open F-Algebra

iterate : ∀ {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C} → F-Algebra F → F-Algebra F
iterate {F = F} F-alg = record { A = Functor.F₀ F $ A F-alg ; α = Functor.F₁ F $ α F-alg }
