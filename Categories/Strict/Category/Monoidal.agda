{-# OPTIONS --without-K --safe #-}
open import Categories.Strict.Category

-- Definition of Strict Monoidal Category

-- (see Categories.Monoidal for more commentary)

module Categories.Strict.Category.Monoidal {o ℓ} (C : Category o ℓ) where

open import Level
open import Function using (_$_)
open import Data.Product using (_×_; _,_; curry′)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Categories.Strict.Functor renaming (id to idF)
open import Categories.Strict.Functor.Bifunctor using (Bifunctor)

open import Categories.Strict.Morphism C using (_≅_; module ≅)

private
  module C = Category C

open C hiding (id; identityˡ; identityʳ; assoc)
open Commutation

private
  variable
    X Y Z W A B : Obj
    f g h i a b : X ⇒ Y

record Monoidal : Set (o ⊔ ℓ) where
  infixr 10 _⊗₀_ _⊗₁_

  field
    ⊗  : Bifunctor C C C
    unit : Obj

  module ⊗ = Functor ⊗

  open Functor ⊗

  _⊗₀_ : Obj → Obj → Obj
  _⊗₀_ = curry′ F₀

  -- this is also 'curry', but a very-dependent version
  _⊗₁_ : X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W
  f ⊗₁ g = F₁ (f , g)

  field
    unitorˡ    : unit ⊗₀ X ≅ X
    unitorʳ    : X ⊗₀ unit ≅ X
    associator : (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)

  module unitorˡ {X} = _≅_ (unitorˡ {X = X})
  module unitorʳ {X} = _≅_ (unitorʳ {X = X})
  module associator {X} {Y} {Z} = _≅_ (associator {X} {Y} {Z})

  -- for exporting, it makes sense to use the above long names, but for
  -- internal consumption, the traditional (short!) categorical names are more
  -- convenient. However, they are not symmetric, even though the concepts are, so
  -- we'll use ⇒ and ⇐ arrows to indicate that

  private
    λ⇒ = unitorˡ.from
    λ⇐ = unitorˡ.to
    ρ⇒ = unitorʳ.from
    ρ⇐ = unitorʳ.to
    α⇒ = associator.from
    α⇐ = associator.to

  field
    unitorˡ-commute-from : CommutativeSquare (C.id ⊗₁ f) λ⇒ λ⇒ f
    unitorˡ-commute-to   : CommutativeSquare f λ⇐ λ⇐ (C.id ⊗₁ f)
    unitorʳ-commute-from : CommutativeSquare (f ⊗₁ C.id) ρ⇒ ρ⇒ f
    unitorʳ-commute-to   : CommutativeSquare f ρ⇐ ρ⇐ (f ⊗₁ C.id)
    assoc-commute-from   : CommutativeSquare ((f ⊗₁ g) ⊗₁ h) α⇒ α⇒ (f ⊗₁ (g ⊗₁ h))
    assoc-commute-to     : CommutativeSquare (f ⊗₁ (g ⊗₁ h)) α⇐ α⇐ ((f ⊗₁ g) ⊗₁ h)
    triangle             : [ (X ⊗₀ unit) ⊗₀ Y ⇒ X ⊗₀ Y ]⟨
                             α⇒           ⇒⟨ X ⊗₀ (unit ⊗₀ Y) ⟩
                             C.id ⊗₁ λ⇒
                           ≡ ρ⇒ ⊗₁ C.id
                           ⟩
    pentagon             : [ ((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W ⇒ X ⊗₀ Y ⊗₀ Z ⊗₀ W ]⟨
                             α⇒ ⊗₁ C.id       ⇒⟨ (X ⊗₀ Y ⊗₀ Z) ⊗₀ W ⟩
                             α⇒               ⇒⟨ X ⊗₀ (Y ⊗₀ Z) ⊗₀ W ⟩
                             C.id ⊗₁ α⇒
                           ≡ α⇒               ⇒⟨ (X ⊗₀ Y) ⊗₀ Z ⊗₀ W ⟩
                             α⇒
                           ⟩
