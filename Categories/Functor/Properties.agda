{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Properties where

open import Categories.Category
open import Categories.Functor.Core
open import Categories.Morphisms

open import Relation.Binary using (_Preserves_⟶_)

module _ {o ℓ e o′ ℓ′ e′}
         {Cc : Category o ℓ e} {Dc : Category o′ ℓ′ e′}
         (F : Functor Cc Dc) where
  module Cc = Category Cc
  module Dc = Category Dc
  open Cc hiding (_∘_)
  open Functor F

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

  [_]-resp-Iso : ∀ {A B} {f : A ⇒ B} {g : B ⇒ A} → Iso Cc f g → Iso Dc (F₁ f) (F₁ g)
  [_]-resp-Iso {f = f} {g} iso = record
    { isoˡ = begin
      F₁ g ∘ F₁ f       ≈⟨ sym homomorphism ⟩
      F₁ (Cc [ g ∘ f ]) ≈⟨ F-resp-≈ isoˡ ⟩
      F₁ Cc.id          ≈⟨ identity ⟩
      Dc.id             ∎
    ; isoʳ = begin
      F₁ f ∘ F₁ g       ≈⟨ sym homomorphism ⟩
      F₁ (Cc [ f ∘ g ]) ≈⟨ F-resp-≈ isoʳ ⟩
      F₁ Cc.id          ≈⟨ identity ⟩
      Dc.id             ∎
    }
    where open Iso iso
          open Dc
          open Dc.HomReasoning
          open Dc.Equiv
          
  [_]-resp-≅ : F₀ Preserves _≅_ Cc ⟶ _≅_ Dc
  [_]-resp-≅ i≅j = record
    { f   = F₁ f
    ; g   = F₁ g
    ; iso = [_]-resp-Iso iso
    }
    where open _≅_ i≅j
