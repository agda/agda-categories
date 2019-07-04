{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Category.Monoidal {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Function using (_$_)
open import Data.Product using (_×_; _,_)

open import Categories.Category.Product
open import Categories.Category.Groupoid
open import Categories.Functor.Bifunctor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation hiding (_≃_) renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
  hiding (unitorˡ; unitorʳ; associator; _≅_) renaming (refl to idNi)
open import Categories.Morphism C
open import Categories.Morphism.Isomorphism C

private
  module C = Category C

open C hiding (id; identityˡ; identityʳ; assoc)
open Commutation

private
  variable
    X Y Z W A B : Obj
    f g h i a b : X ⇒ Y

record Monoidal : Set (o ⊔ ℓ ⊔ e) where
  infixr 10 _⊗₀_ _⊗₁_ _⊗ᵢ_

  field
    ⊗  : Bifunctor C C C
    unit : Obj

  open Functor ⊗

  _⊗₀_ : Obj → Obj → Obj
  X ⊗₀ Y = F₀ (X , Y)

  _⊗₁_ : X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W
  f ⊗₁ g = F₁ (f , g)

  _⊗- : Obj → Functor C C
  X ⊗- = appˡ ⊗ X

  -⊗_ : Obj → Functor C C
  -⊗ X = appʳ ⊗ X

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
    triangle             : [ (X ⊗₀ unit) ⊗₀ Y ⇒ X ⊗₀ Y ]⟨
                             associator.from           ⇒⟨ X ⊗₀ (unit ⊗₀ Y) ⟩
                             C.id ⊗₁ unitorˡ.from
                           ≈ unitorʳ.from ⊗₁ C.id
                           ⟩
    pentagon             : [ ((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W ⇒ X ⊗₀ Y ⊗₀ Z ⊗₀ W ]⟨
                             associator.from ⊗₁ C.id                 ⇒⟨ (X ⊗₀ Y ⊗₀ Z) ⊗₀ W ⟩
                             associator.from                         ⇒⟨ X ⊗₀ (Y ⊗₀ Z) ⊗₀ W ⟩
                             C.id ⊗₁ associator.from
                           ≈ associator.from                         ⇒⟨ (X ⊗₀ Y) ⊗₀ Z ⊗₀ W ⟩
                             associator.from
                           ⟩

  private
    [x⊗y]⊗z : Bifunctor (Product C C) C C
    [x⊗y]⊗z = ⊗ ∘F (⊗ ⁂ idF)

    x⊗[y⊗z] : Bifunctor (Product C C) C C
    x⊗[y⊗z] = ⊗ ∘F (idF ⁂ ⊗) ∘F assocˡ _ _ _

  unitorˡ-naturalIsomorphism : NaturalIsomorphism (unit ⊗-) idF
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

  unitorʳ-naturalIsomorphism : NaturalIsomorphism (-⊗ unit) idF
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

  module unitorˡ-natural = NaturalIsomorphism unitorˡ-naturalIsomorphism
  module unitorʳ-natural = NaturalIsomorphism unitorʳ-naturalIsomorphism
  module associator-natural = NaturalIsomorphism associator-naturalIsomorphism

  _⊗ᵢ_ : X ≅ Y → Z ≅ W → X ⊗₀ Z ≅ Y ⊗₀ W
  f ⊗ᵢ g = [ ⊗ ]-resp-≅ record
    { from = from f , from g
    ; to   = to f , to g
    ; iso  = record
      { isoˡ = isoˡ f , isoˡ g
      ; isoʳ = isoʳ f , isoʳ g
      }
    }
    where open _≅_

  triangle-iso : ≅-refl ⊗ᵢ unitorˡ ∘ᵢ associator ≃ unitorʳ {X} ⊗ᵢ ≅-refl {Y}
  triangle-iso = lift-triangle′ triangle

  pentagon-iso : ≅-refl ⊗ᵢ associator ∘ᵢ associator ∘ᵢ associator {X} {Y} {Z} ⊗ᵢ ≅-refl {W} ≃ associator ∘ᵢ associator
  pentagon-iso = lift-pentagon′ pentagon

  refl⊗refl≃refl : ≅-refl {A} ⊗ᵢ ≅-refl {B} ≃ ≅-refl
  refl⊗refl≃refl = record
    { from-≈ = identity
    ; to-≈   = identity
    }
