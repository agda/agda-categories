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

  module _ (F : Endofunctor C) where
    open Category C
    open Functor F
    F-Algebra-on : Obj → Set ℓ
    F-Algebra-on A = F₀ A ⇒ A

  record F-Algebra (F : Endofunctor C) : Set (o ⊔ ℓ) where
    open Category C
    field
      A : Obj
      α : F-Algebra-on F A

  to-Algebra : {A : Category.Obj C} → {F : Endofunctor C} → (F-Algebra-on F A) → (F-Algebra F)
  to-Algebra {A = A} α = record {A = A; α = α}

  open F-Algebra

  -- Given an F-Algebra F, one can apply F to it to obtain an new 'iterated' F-Algebra
  iterate : {F : Endofunctor C} → F-Algebra F → F-Algebra F
  iterate {F} c = record { A = Functor.F₀ F $ A c ; α = Functor.F₁ F $ α c }

  module _ {F : Endofunctor C} (X Y : F-Algebra F) where
    open Category C using (_⇒_; _∘_; _≈_)
    open Functor F using (F₁)
    private
      module X = F-Algebra X
      module Y = F-Algebra Y
    is-F-Algebra-Morphism : (X.A ⇒ Y.A) → (Set e)
    is-F-Algebra-Morphism f = f ∘ X.α ≈ Y.α ∘ F₁ f

    record F-Algebra-Morphism : Set (ℓ ⊔ e) where
      field
        f : X.A ⇒ Y.A
        commutes : is-F-Algebra-Morphism f
