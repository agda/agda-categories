{-# OPTIONS --without-K --safe #-}
module Categories.Category where

open import Level

-- The main definitions are in:
open import Categories.Category.Core public

private
  variable
    o ℓ e : Level

-- Convenience functions for working over mupliple categories at once:
-- C [ x , y ] (for x y objects of C) - Hom_C(x , y)
-- C [ f ≈ g ] (for f g arrows of C)  - that f and g are equivalent arrows
-- C [ f ∘ g ] (for f g composables arrows of C) - composition in C
infix 10  _[_,_] _[_≈_] _[_∘_]

_[_,_] : (C : Category o ℓ e) → (X : Category.Obj C) → (Y : Category.Obj C) → Set ℓ
_[_,_] = Category._⇒_

_[_≈_] : (C : Category o ℓ e) → ∀ {X Y} (f g : C [ X , Y ]) → Set e
_[_≈_] = Category._≈_

_[_∘_] : (C : Category o ℓ e) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
_[_∘_] = Category._∘_

module Definitions (𝓒 : Category o ℓ e) where
  open Category 𝓒

  CommutativeSquare : {A B C D : Obj} → (f : A ⇒ B) (g : A ⇒ C) (h : B ⇒ D) (i : C ⇒ D) → Set _
  CommutativeSquare f g h i = h ∘ f ≈ i ∘ g
