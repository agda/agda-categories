{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Properties where

open import Categories.Category
open import Categories.Functor.Core

module _ {o ℓ e o′ ℓ′ e′}
         {Cc : Category o ℓ e} {Dc : Category o′ ℓ′ e′}
         (F : Functor Cc Dc) where
  module Cc = Category Cc
  module Dc = Category Dc
  open Cc hiding (_∘_)
  open Functor F using (F₁ ; homomorphism ; F-resp-≈)

  module _ {A B C D : Obj}
           {f : A ⇒ B} {g : A ⇒ C} {h : B ⇒ D} {i : C ⇒ D} where

    [_]-resp-square : Cc.CommutativeSquare f g h i →
                      Dc.CommutativeSquare (F₁ f) (F₁ g) (F₁ h) (F₁ i)
    [_]-resp-square sq = begin
      F₁ h ∘ F₁ f       ≈⟨ Dc.Equiv.sym homomorphism ⟩
      F₁ (Cc [ h ∘ f ]) ≈⟨ F-resp-≈ sq ⟩
      F₁ (Cc [ i ∘ g ]) ≈⟨ homomorphism ⟩
      F₁ i ∘ F₁ g       ∎
      where open Dc
            open Dc.HomReasoning
