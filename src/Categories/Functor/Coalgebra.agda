{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Coalgebra where

-- Co-algebras of a Functor
open import Level
open import Function using (_$_)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor)

record F-Coalgebra {o ℓ e} {C : Category o ℓ e} (F : Endofunctor C) : Set (o ⊔ ℓ) where
  open Category C
  field
    A : Obj
    α : A ⇒ Functor.F₀ F A

open F-Coalgebra

-- Given a F-Coalgebra F, one can apply F to it to obtain an new 'iterated' F-Coalgebra
iterate : ∀ {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C} → F-Coalgebra F → F-Coalgebra F
iterate {F = F} F-alg = record { A = Functor.F₀ F $ A F-alg ; α = Functor.F₁ F $ α F-alg }
