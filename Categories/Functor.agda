{-# OPTIONS --without-K --safe #-}
module Categories.Functor where

open import Level
open import Categories.Category
open import Categories.Functor.Core public
open import Data.Product using (_×_)
open import Function.Surjection using (Surjection)

open import Relation.Nullary

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D : Category o ℓ e

Contravariant : ∀ (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Set _
Contravariant C D = Functor (Category.op C) D

Faithful : Functor C D → Set _
Faithful {C = C} {D = D} F = ∀ {X Y} → (f g : C [ X , Y ]) → D [ F₁ f ≈ F₁ g ] → C [ f ≈ g ]
  where open Functor F

Full : Functor C D → Set _
Full {C = C} {D = D} F = ∀ {X Y} → Surjection (C.hom-setoid {X} {Y}) (D.hom-setoid {F₀ X} {F₀ Y})
  where
    module C = Category C
    module D = Category D
    open Functor F

FullyFaithful : Functor C D → Set _
FullyFaithful F = Full F × Faithful F
