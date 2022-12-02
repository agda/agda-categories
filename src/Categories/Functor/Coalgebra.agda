{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Coalgebra where

-- Co-algebras of a Functor
open import Level
open import Function using (_$_)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor)

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} where

  F-Coalgebra-on : Endofunctor C → C .Category.Obj → Set ℓ
  F-Coalgebra-on F A = A ⇒ F₀ A where open Category C; open Functor F

  record F-Coalgebra (F : Endofunctor C) : Set (o ⊔ ℓ) where
    open Category C
    field
      A : Obj
      α : F-Coalgebra-on F A

  open F-Coalgebra

  -- Given a F-Coalgebra F, one can apply F to it to obtain an new 'iterated' F-Coalgebra
  iterate : {F : Endofunctor C} → F-Coalgebra F → F-Coalgebra F
  iterate {F = F} F-alg = record { A = Functor.F₀ F $ A F-alg ; α = Functor.F₁ F $ α F-alg }

  module _ {F : Endofunctor C} (X Y : F-Coalgebra F) where
    open Category C using (_⇒_; _∘_; _≈_)
    open Functor F using (F₁)
    private
      module X = F-Coalgebra X
      module Y = F-Coalgebra Y
    is-F-Coalgebra-Morphism : (X.A ⇒ Y.A) → (Set e)
    is-F-Coalgebra-Morphism f = Y.α ∘ f ≈ F₁ f ∘ X.α

    record F-Coalgebra-Morphism : Set (ℓ ⊔ e) where
      field
        f : X.A ⇒ Y.A
        commutes : is-F-Coalgebra-Morphism f
