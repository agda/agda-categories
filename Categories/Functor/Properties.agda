{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Properties where

open import Level

open import Categories.Category
open import Categories.Functor.Core
open import Categories.Morphism
open import Categories.Morphism.IsoEquiv as IsoEquiv
open import Categories.Morphism.Isomorphism

open import Relation.Binary using (_Preserves_⟶_)

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

module _ (F : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module IsoC = IsoEquiv C
    module IsoD = IsoEquiv D
  open C hiding (_∘_)
  open Functor F

  private
    variable
      A B E : Obj
      f g h i : A ⇒ B

  [_]-resp-∘ : C [ C [ f ∘ g ] ≈ h ] → D [ D [ F₁ f ∘ F₁ g ] ≈ F₁ h ]
  [_]-resp-∘ {f = f} {g = g} {h = h} eq = begin
    F₁ f ∘ F₁ g      ≈˘⟨ homomorphism ⟩
    F₁ (C [ f ∘ g ]) ≈⟨ F-resp-≈ eq ⟩
    F₁ h             ∎
    where open D
          open D.HomReasoning

  [_]-resp-square : C.CommutativeSquare f g h i →
                    D.CommutativeSquare (F₁ f) (F₁ g) (F₁ h) (F₁ i)
  [_]-resp-square {f = f} {g = g} {h = h} {i = i} sq = begin
    F₁ h ∘ F₁ f      ≈˘⟨ homomorphism ⟩
    F₁ (C [ h ∘ f ]) ≈⟨ F-resp-≈ sq ⟩
    F₁ (C [ i ∘ g ]) ≈⟨ homomorphism ⟩
    F₁ i ∘ F₁ g       ∎
    where open D
          open D.HomReasoning

  [_]-resp-Iso : Iso C f g → Iso D (F₁ f) (F₁ g)
  [_]-resp-Iso {f = f} {g = g} iso = record
    { isoˡ = begin
      F₁ g ∘ F₁ f      ≈⟨ [ isoˡ ]-resp-∘ ⟩
      F₁ C.id          ≈⟨ identity ⟩
      D.id             ∎
    ; isoʳ = begin
      F₁ f ∘ F₁ g      ≈⟨ [ isoʳ ]-resp-∘ ⟩
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
    ; iso        = [ iso ]-resp-Iso
    }
    where open _≅_ i≅j

  [_]-resp-≃ : ∀ {f g :  _≅_ C A B} → f IsoC.≃ g → [ f ]-resp-≅ IsoD.≃ [ g ]-resp-≅
  [_]-resp-≃ eq = record
    { from-≈ = F-resp-≈ from-≈
    ; to-≈   = F-resp-≈ to-≈
    }
    where open _≃_ eq

  homomorphismᵢ : ∀ {f : _≅_ C B E} {g : _≅_ C A B} → [ _∘ᵢ_ C f g ]-resp-≅ IsoD.≃ (_∘ᵢ_ D [ f ]-resp-≅ [ g ]-resp-≅ )
  homomorphismᵢ = record
    { from-≈ = homomorphism
    ; to-≈   = homomorphism
    }
