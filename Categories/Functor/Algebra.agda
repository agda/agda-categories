{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Algebra where

-- Algebra for a Functor

open import Level
open import Function using (_$_)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor)

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} where

  record F-Algebra (F : Endofunctor C) : Set (o ⊔ ℓ) where
    open Category C
    field
      A : Obj
      α : Functor.F₀ F A ⇒ A

  open F-Algebra

  -- Given an F-Algebra F, one can apply F to it to obtain an new 'iterated' F-Algebra
  iterate : {F : Endofunctor C} → F-Algebra F → F-Algebra F
  iterate {F} c = record { A = Functor.F₀ F $ A c ; α = Functor.F₁ F $ α c }

  record F-Algebra-Morphism {F : Endofunctor C} (X Y : F-Algebra F) : Set (ℓ ⊔ e) where
    open Category C
    module X = F-Algebra X
    module Y = F-Algebra Y
    open Functor F
    field
      f : X.A ⇒ Y.A
      commutes : f ∘ X.α ≈ Y.α ∘ F₁ f
