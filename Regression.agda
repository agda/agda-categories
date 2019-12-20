{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Regression {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Product using (_×_; _,_; curry′)

open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Morphism C using (_≅_)

private
  module C = Category C

open C hiding (id; identityˡ; identityʳ; assoc)

private
  variable
    X Y Z W : Obj
    f g h : X ⇒ Y

record Monoidal : Set (o ⊔ ℓ ⊔ e) where
  infixr 10 _⊗₀_ _⊗₁_

  field
    ⊗  : Bifunctor C C C

  module ⊗ = Functor ⊗

  open Functor ⊗

  _⊗₀_ : Obj → Obj → Obj
  _⊗₀_ = curry′ F₀

  -- this is also 'curry', but a very-dependent version
  _⊗₁_ : X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W
  f ⊗₁ g = F₁ (f , g)

  field
    associator : (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)

  module associator {X} {Y} {Z} = _≅_ (associator {X} {Y} {Z})

  -- for exporting, it makes sense to use the above long names, but for
  -- internal consumption, the traditional (short!) categorical names are more
  -- convenient. However, they are not symmetric, even though the concepts are, so
  -- we'll use ⇒ and ⇐ arrows to indicate that
  private
    α⇒ = associator.from
    α⇐ = λ {X} {Y} {Z} → associator.to {X} {Y} {Z}

  field
    -- assoc-commute-from   : CommutativeSquare ((f ⊗₁ g) ⊗₁ h) α⇒ α⇒ (f ⊗₁ (g ⊗₁ h))
    assoc-commute-to     : CommutativeSquare (f ⊗₁ (g ⊗₁ h)) α⇐ α⇐ ((f ⊗₁ g) ⊗₁ h)
