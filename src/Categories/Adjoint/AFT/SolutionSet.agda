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


record SolutionSet′ : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    S₀      : ∀ {A X} → X ⇒ F₀ A → C.Obj
    S₁      : ∀ {A X} (f : X ⇒ F₀ A) → S₀ f C.⇒ A
    ϕ       : ∀ {A X} (f : X ⇒ F₀ A) → X ⇒ F₀ (S₀ f)
    commute : ∀ {A X} (f : X ⇒ F₀ A) → F₁ (S₁ f) ∘ ϕ f ≈ f

SolutionSet⇒SolutionSet′ : ∀ {i} → SolutionSet i → SolutionSet′
SolutionSet⇒SolutionSet′ s = record
  { S₀      = λ f → S (S₀ f)
  ; S₁      = S₁
  ; ϕ       = ϕ
  ; commute = commute
  }
  where open SolutionSet s

SolutionSet′⇒SolutionSet : ∀ i → SolutionSet′ → SolutionSet (o ⊔ i)
SolutionSet′⇒SolutionSet i s = record
  { I       = Lift i C.Obj
  ; S       = lower
  ; S₀      = λ f → lift (S₀ f)
  ; S₁      = S₁
  ; ϕ       = ϕ
  ; commute = commute
  }
  where open SolutionSet′ s
