{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor

module Categories.Adjoint.AFT.SolutionSet {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
                                          (F : Functor C D) where

open import Level

private
  module C = Category C
  module D = Category D
  module F = Functor F
  open D
  open F

record SolutionSet i : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ (suc i)) where
  field
    I       : Set i
    S       : I → C.Obj
    S₀      : ∀ {A X} → X ⇒ F₀ A → I
    S₁      : ∀ {A X} (f : X ⇒ F₀ A) → S (S₀ f) C.⇒ A
    ϕ       : ∀ {A X} (f : X ⇒ F₀ A) → X ⇒ F₀ (S (S₀ f))
    commute : ∀ {A X} (f : X ⇒ F₀ A) → F₁ (S₁ f) ∘ ϕ f ≈ f
