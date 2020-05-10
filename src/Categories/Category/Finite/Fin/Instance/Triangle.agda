{-# OPTIONS --without-K --safe #-}

module Categories.Category.Finite.Fin.Instance.Triangle where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality.Core as ≡

open import Categories.Category.Finite.Fin
open import Categories.Category.Core

private
  variable
    a b c d : Fin 3

-- the diagram is the following:
--
--  0
--  | \
--  |  \
--  |   \
--  |    \
--  v     v
--  1 ---> 2
--
-- all morphisms are 0 (because there is at most one morphism between each pair of objects).
TriangleShape : FinCatShape
TriangleShape = shapeHelper record
  { size      = 3
  ; ∣_⇒_∣     = morph
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  }
  where morph : Fin 3 → Fin 3 → ℕ
        morph 0F 0F = 1
        morph 0F 1F = 1
        morph 0F 2F = 1
        morph 1F 1F = 1
        morph 1F 2F = 1
        morph 2F 2F = 1
        morph _ _   = 0

        id : Fin (morph a a)
        id {0F} = 0F
        id {1F} = 0F
        id {2F} = 0F

        _∘_ : ∀ {a b c} → Fin (morph b c) → Fin (morph a b) → Fin (morph a c)
        _∘_ {0F} {0F} {0F} 0F 0F = 0F
        _∘_ {0F} {0F} {1F} 0F 0F = 0F
        _∘_ {0F} {0F} {2F} 0F 0F = 0F
        _∘_ {0F} {1F} {1F} 0F 0F = 0F
        _∘_ {0F} {1F} {2F} 0F 0F = 0F
        _∘_ {0F} {2F} {2F} 0F 0F = 0F
        _∘_ {1F} {1F} {1F} 0F 0F = 0F
        _∘_ {1F} {1F} {2F} 0F 0F = 0F
        _∘_ {1F} {2F} {2F} 0F 0F = 0F
        _∘_ {2F} {2F} {2F} 0F 0F = 0F

        assoc : ∀ {f : Fin (morph a b)} {g : Fin (morph b c)} {h : Fin (morph c d)} →
                  ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
        assoc {0F} {0F} {0F} {0F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {0F} {1F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {0F} {2F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {1F} {1F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {1F} {2F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {2F} {2F} {0F} {0F} {0F} = refl
        assoc {0F} {1F} {1F} {1F} {0F} {0F} {0F} = refl
        assoc {0F} {1F} {1F} {2F} {0F} {0F} {0F} = refl
        assoc {0F} {1F} {2F} {2F} {0F} {0F} {0F} = refl
        assoc {0F} {2F} {2F} {2F} {0F} {0F} {0F} = refl
        assoc {1F} {1F} {1F} {1F} {0F} {0F} {0F} = refl
        assoc {1F} {1F} {1F} {2F} {0F} {0F} {0F} = refl
        assoc {1F} {1F} {2F} {2F} {0F} {0F} {0F} = refl
        assoc {1F} {2F} {2F} {2F} {0F} {0F} {0F} = refl
        assoc {2F} {2F} {2F} {2F} {0F} {0F} {0F} = refl

        identityˡ : ∀ {f : Fin (morph a b)} → (id ∘ f) ≡ f
        identityˡ {0F} {0F} {0F} = refl
        identityˡ {0F} {1F} {0F} = refl
        identityˡ {0F} {2F} {0F} = refl
        identityˡ {1F} {1F} {0F} = refl
        identityˡ {1F} {2F} {0F} = refl
        identityˡ {2F} {2F} {0F} = refl

        identityʳ : ∀ {f : Fin (morph a b)} → (f ∘ id) ≡ f
        identityʳ {0F} {0F} {0F} = refl
        identityʳ {0F} {1F} {0F} = refl
        identityʳ {0F} {2F} {0F} = refl
        identityʳ {1F} {1F} {0F} = refl
        identityʳ {1F} {2F} {0F} = refl
        identityʳ {2F} {2F} {0F} = refl

Triangle : Category _ _ _
Triangle = FinCategory TriangleShape

module Triangle = Category Triangle
