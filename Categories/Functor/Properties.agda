{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Properties where

open import Level

open import Categories.Category
open import Categories.Functor.Core
open import Categories.Morphism

open import Relation.Binary using (_Preserves_⟶_)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D : Category o ℓ e

module _ (F : Functor C D) where
  private
    module C = Category C
    module D = Category D
  open C hiding (_∘_)
  open Functor F

  private
    variable
      A B : Obj
      f g h i : A ⇒ B

  [_]-resp-square : C.CommutativeSquare f g h i →
                    D.CommutativeSquare (F₁ f) (F₁ g) (F₁ h) (F₁ i)
  [_]-resp-square {f = f} {g = g} {h = h} {i = i} sq = begin
    F₁ h ∘ F₁ f       ≈⟨ D.Equiv.sym homomorphism ⟩
    F₁ (C [ h ∘ f ]) ≈⟨ F-resp-≈ sq ⟩
    F₁ (C [ i ∘ g ]) ≈⟨ homomorphism ⟩
    F₁ i ∘ F₁ g       ∎
    where open D
          open D.HomReasoning

  [_]-resp-Iso : Iso C f g → Iso D (F₁ f) (F₁ g)
  [_]-resp-Iso {f = f} {g = g} iso = record
    { isoˡ = begin
      F₁ g ∘ F₁ f       ≈⟨ sym homomorphism ⟩
      F₁ (C [ g ∘ f ]) ≈⟨ F-resp-≈ isoˡ ⟩
      F₁ C.id          ≈⟨ identity ⟩
      D.id             ∎
    ; isoʳ = begin
      F₁ f ∘ F₁ g       ≈⟨ sym homomorphism ⟩
      F₁ (C [ f ∘ g ]) ≈⟨ F-resp-≈ isoʳ ⟩
      F₁ C.id          ≈⟨ identity ⟩
      D.id             ∎
    }
    where open Iso iso
          open D
          open D.HomReasoning
          
  [_]-resp-≅ : F₀ Preserves _≅_ C ⟶ _≅_ D
  [_]-resp-≅ i≅j = record
    { from       = F₁ from
    ; to         = F₁ to
    ; iso        = [_]-resp-Iso iso
    }
    where open _≅_ i≅j
