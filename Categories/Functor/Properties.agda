{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Properties where

open import Categories.Category
open import Categories.Functor.Core hiding (_∘_) 

private 
  square-functorial-prop : ∀ {o ℓ e o′ ℓ′ e′}
                             {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
                             (F : Functor C D) →
                             Set _
  square-functorial-prop {C = Cc} {Dc} F =
    ∀ {A B C D : Obj} {f : A ⇒ B} {g : A ⇒ C} {h : B ⇒ D} {i : C ⇒ D} →
      Category.CommutativeSquare Cc f g h i →
      Category.CommutativeSquare Dc (F₁ f) (F₁ g) (F₁ h) (F₁ i)
    where open Category Cc hiding (CommutativeSquare)
          open Functor F using (F₁)

square-functorial : ∀ {o ℓ e o′ ℓ′ e′}
                      {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
                      (F : Functor C D) →
                      square-functorial-prop F
square-functorial {C = C} {D} F {f = f} {g} {h} {i} sq = begin
  F₁ h ∘ F₁ f      ≈⟨ Equiv.sym homomorphism ⟩
  F₁ (C [ h ∘ f ]) ≈⟨ F-resp-≈ sq ⟩
  F₁ (C [ i ∘ g ]) ≈⟨ homomorphism ⟩
  F₁ i ∘ F₁ g      ∎
  where open Category D
        open Functor F using (F₁ ; homomorphism ; F-resp-≈)
        open HomReasoning
