{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Category.Monoidal {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Product using (_×_; _,_)

open import Categories.Category.Product
open import Categories.Functor.Bifunctor renaming (id to idF)
open import Categories.NaturalTransformation hiding (unitorˡ; unitorʳ; associator) renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≅_) renaming (refl to idNi)
open import Categories.Morphism C

private
  module C = Category C

open C hiding (id; identityˡ; identityʳ; assoc)

private
  variable
    X Y Z W A B : Obj
    f g h i a b : X ⇒ Y

record Monoidal : Set (o ⊔ ℓ ⊔ e) where
  infixr 10 _⊗₀_ _⊗₁_
  
  field
    ⊗  : Bifunctor C C C
    unit : Obj

  open Functor ⊗

  _⊗₀_ : Obj → Obj → Obj
  X ⊗₀ Y = F₀ (X , Y)

  _⊗₁_ : X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W
  f ⊗₁ g = F₁ (f , g)

  field
    unitorˡ    : unit ⊗₀ X ≅ X
    unitorʳ    : X ⊗₀ unit ≅ X
    associator : (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)

  module unitorˡ {X} = _≅_ (unitorˡ {X = X})
  module unitorʳ {X} = _≅_ (unitorʳ {X = X})
  module associator {X} {Y} {Z} = _≅_ (associator {X} {Y} {Z})

  field
    unitorˡ-commute-from : CommutativeSquare (C.id ⊗₁ f) unitorˡ.from unitorˡ.from f
    unitorˡ-commute-to   : CommutativeSquare f unitorˡ.to unitorˡ.to (C.id ⊗₁ f)
    unitorʳ-commute-from : CommutativeSquare (f ⊗₁ C.id) unitorʳ.from unitorʳ.from f
    unitorʳ-commute-to   : CommutativeSquare f unitorʳ.to unitorʳ.to (f ⊗₁ C.id)
    assoc-commute-from   : CommutativeSquare ((f ⊗₁ g) ⊗₁ h) associator.from associator.from (f ⊗₁ (g ⊗₁ h))
    assoc-commute-to     : CommutativeSquare (f ⊗₁ (g ⊗₁ h)) associator.to associator.to ((f ⊗₁ g) ⊗₁ h)

  private
    [x⊗y]⊗z : Bifunctor (Product C C) C C
    [x⊗y]⊗z = ⊗ ∘F (⊗ ⁂ idF)

    x⊗[y⊗z] : Bifunctor (Product C C) C C
    x⊗[y⊗z] = ⊗ ∘F (idF ⁂ ⊗) ∘F assocˡ _ _ _

  unitorˡ-naturalIsomorphism : NaturalIsomorphism (appˡ ⊗ unit) idF
  unitorˡ-naturalIsomorphism = record
    { F⇒G = record
      { η       = λ X → unitorˡ.from
      ; commute = λ f → unitorˡ-commute-from
      }
    ; F⇐G = record
      { η       = λ X → unitorˡ.to
      ; commute = λ f → unitorˡ-commute-to
      }
    ; iso = λ _ → unitorˡ.iso
    }

  unitorʳ-naturalIsomorphism : NaturalIsomorphism (appʳ ⊗ unit) idF
  unitorʳ-naturalIsomorphism = record
    { F⇒G = record
      { η       = λ X → unitorʳ.from
      ; commute = λ f → unitorʳ-commute-from
      }
    ; F⇐G = record
      { η       = λ X → unitorʳ.to
      ; commute = λ f → unitorʳ-commute-to
      }
    ; iso = λ _ → unitorʳ.iso
    }

  associator-naturalIsomorphism : NaturalIsomorphism [x⊗y]⊗z x⊗[y⊗z]
  associator-naturalIsomorphism = record
    { F⇒G = record
      { η       = λ where
        ((X , Y) , Z) → associator.from
      ; commute = λ where
        ((f , g) , h) → assoc-commute-from
      }
    ; F⇐G = record
      { η       = λ where
        ((X , Y) , Z) → associator.to
      ; commute = λ where
        ((f , g) , h) → assoc-commute-to
      }
    ; iso = λ _ → associator.iso
    }

  field
    triangle : unitorʳ.from ⊗₁ (C.id {X}) ≈ C.id {Y} ⊗₁ unitorˡ.from ∘ associator.from
    pentagon : C.id {X} ⊗₁ associator.from {Y} {Z} ∘ associator.from ∘ associator.from ⊗₁ C.id {W}
             ≈ associator.from ∘ associator.from 

