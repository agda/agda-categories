{-# OPTIONS --without-K --safe #-}
module Categories.Strict.Functor.Properties where

-- Properties valid of all Functors
open import Level

open import Categories.Strict.Category
open import Categories.Strict.Functor
open import Categories.Strict.Morphism
open import Categories.Strict.Morphism.IsoEquiv as IsoEquiv
-- open import Categories.Strict.Morphism.Isomorphism

open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

private
  variable
    o ℓ : Level
    C D : Category o ℓ

-- a series of [ Functor ]-respects-Thing combinators (with respects -> resp)

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

  [_]-resp-∘ : C [ f ∘ g ] ≡ h → D [ F₁ f ∘ F₁ g ] ≡ F₁ h
  [_]-resp-∘ {f = f} {g = g} {h = h} eq = begin
    F₁ f ∘ F₁ g      ≈˘⟨ homomorphism ⟩
    F₁ (C [ f ∘ g ]) ≈⟨ cong F₁ eq ⟩
    F₁ h             ∎
    where open D
          open D.HomReasoning

  [_]-resp-square : C.CommutativeSquare f g h i →
                    D.CommutativeSquare (F₁ f) (F₁ g) (F₁ h) (F₁ i)
  [_]-resp-square {f = f} {g = g} {h = h} {i = i} sq = begin
    F₁ h ∘ F₁ f      ≈˘⟨ homomorphism ⟩
    F₁ (C [ h ∘ f ]) ≈⟨ cong F₁ sq ⟩
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
    { from-≈ = cong F₁ from-≈
    ; to-≈   = cong F₁ to-≈
    }
    where open _≃_ eq
{-
  homomorphismᵢ : ∀ {f : _≅_ C B E} {g : _≅_ C A B} → [ _∘ᵢ_ C f g ]-resp-≅ IsoD.≃ (_∘ᵢ_ D [ f ]-resp-≅ [ g ]-resp-≅ )
  homomorphismᵢ = record
    { from-≈ = homomorphism
    ; to-≈   = homomorphism
    }
-}
-- Functor Composition is Associative and the unit laws are found in
-- NaturalTransformation.NaturalIsomorphism, reified as associator, unitorˡ and unitorʳ.
