{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- Definition of Monoidal Category

-- Big design decision that differs from the previous version:
-- Do not go through "Functor.Power" to encode variables and work
-- at the level of NaturalIsomorphisms, instead work at the object/morphism
-- level, via the more direct _⊗₀_ _⊗₁_ _⊗- -⊗_.
-- The original design needed quite a few contortions to get things working,
-- but these are simply not needed when working directly with the morphisms.
--
-- Smaller design decision: export some items with long names
-- (unitorˡ, unitorʳ and associator), but internally work with the more classical
-- short greek names (λ, ρ and α respectively).

module Categories.Category.Monoidal {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Function using (_$_)
open import Data.Product using (_×_; _,_; curry′)

open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
  hiding (unitorˡ; unitorʳ; associator; _≃_)
open import Categories.Morphism C using (_≅_; module ≅)
open import Categories.Morphism.IsoEquiv C using (_≃_)
open import Categories.Morphism.Isomorphism C using (_∘ᵢ_; lift-triangle′; lift-pentagon′)

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

  module ⊗ = Functor ⊗

  open Functor ⊗

  _⊗₀_ : Obj → Obj → Obj
  _⊗₀_ = curry′ F₀

  -- this is also 'curry', but a very-dependent version
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
                           ≈ ρ⇒ ⊗₁ C.id
                           ⟩
    pentagon             : [ ((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W ⇒ X ⊗₀ Y ⊗₀ Z ⊗₀ W ]⟨
                             α⇒ ⊗₁ C.id       ⇒⟨ (X ⊗₀ Y ⊗₀ Z) ⊗₀ W ⟩
                             α⇒               ⇒⟨ X ⊗₀ (Y ⊗₀ Z) ⊗₀ W ⟩
                             C.id ⊗₁ α⇒
                           ≈ α⇒               ⇒⟨ (X ⊗₀ Y) ⊗₀ Z ⊗₀ W ⟩
                             α⇒
                           ⟩

  private
    [x⊗y]⊗z : Bifunctor (Product C C) C C
    [x⊗y]⊗z = ⊗ ∘F (⊗ ⁂ idF)

    -- note how this one needs re-association to typecheck (i.e. be correct)
    x⊗[y⊗z] : Bifunctor (Product C C) C C
    x⊗[y⊗z] = ⊗ ∘F (idF ⁂ ⊗) ∘F assocˡ _ _ _

  -- All the implicits below can be inferred, but being explicit is clearer
  unitorˡ-naturalIsomorphism : NaturalIsomorphism (unit ⊗-) idF
  unitorˡ-naturalIsomorphism = record
    { F⇒G = record
      { η       = λ X → λ⇒ {X}
      ; commute = λ f → unitorˡ-commute-from {f = f}
      }
    ; F⇐G = record
      { η       = λ X → λ⇐ {X}
      ; commute = λ f → unitorˡ-commute-to {f = f}
      }
    ; iso = λ X →  unitorˡ.iso {X}
    }

  unitorʳ-naturalIsomorphism : NaturalIsomorphism (-⊗ unit) idF
  unitorʳ-naturalIsomorphism = record
    { F⇒G = record
      { η       = λ X → ρ⇒ {X}
      ; commute = λ f → unitorʳ-commute-from {f = f}
      }
    ; F⇐G = record
      { η       = λ X → ρ⇐ {X}
      ; commute = λ f → unitorʳ-commute-to {f = f}
      }
    ; iso = λ X → unitorʳ.iso {X}
    }

  -- skippinf the explicit arguments here, it does not increase understandability
  associator-naturalIsomorphism : NaturalIsomorphism [x⊗y]⊗z x⊗[y⊗z]
  associator-naturalIsomorphism = record
    { F⇒G = record
      { η       = λ { ((X , Y) , Z) → α⇒ {X} {Y} {Z}}
      ; commute = λ _ → assoc-commute-from
      }
    ; F⇐G = record
      { η       = λ _ → α⇐
      ; commute = λ _ → assoc-commute-to
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

  triangle-iso : ≅.refl ⊗ᵢ unitorˡ ∘ᵢ associator ≃ unitorʳ {X} ⊗ᵢ ≅.refl {Y}
  triangle-iso = lift-triangle′ triangle

  pentagon-iso :
      ≅.refl ⊗ᵢ associator ∘ᵢ associator ∘ᵢ associator {X} {Y} {Z} ⊗ᵢ ≅.refl {W}
    ≃ associator ∘ᵢ associator
  pentagon-iso = lift-pentagon′ pentagon

  refl⊗refl≃refl : ≅.refl {A} ⊗ᵢ ≅.refl {B} ≃ ≅.refl
  refl⊗refl≃refl = record
    { from-≈ = identity
    ; to-≈   = identity
    }
