{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal.Core using (Monoidal)

module Categories.Category.Monoidal.Utilities {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Level
open import Function using (_$_)
open import Algebra.Bundles using (Monoid)
open import Data.Product using (_×_; _,_; curry′)

open import Categories.Category.Product
import Categories.Category.Construction.Core as Core
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
  hiding (unitorˡ; unitorʳ; associator; _≃_)

open import Categories.Morphism.Isomorphism C using (lift-triangle′; lift-pentagon′)
open import Categories.Morphism.Reasoning C
import Categories.Morphism C as Morphism

private
  module C = Category C

open C hiding (identityˡ; identityʳ; assoc)
open Commutation C
open Core.Shorthands C

private
  variable
    X Y Z W A B : Obj
    f g h i a b : X ⇒ Y

open Monoidal M

-- for exporting, it makes sense to use the above long names, but for
-- internal consumption, the traditional (short!) categorical names are more
-- convenient. However, they are not symmetric, even though the concepts are, so
-- we'll use ⇒ and ⇐ arrows to indicate that

module Shorthands where

  λ⇒ = unitorˡ.from
  λ⇐ = unitorˡ.to
  ρ⇒ = unitorʳ.from
  ρ⇐ = unitorʳ.to
  -- eta expansion fixes a problem in 2.6.1, will be reported
  α⇒ = λ {X} {Y} {Z} → associator.from {X} {Y} {Z}
  α⇐ = λ {X} {Y} {Z} → associator.to {X} {Y} {Z}

open Shorthands

private
  [x⊗y]⊗z : Bifunctor (Product C C) C C
  [x⊗y]⊗z = ⊗ ∘F (⊗ ⁂ idF)

  -- note how this one needs re-association to typecheck (i.e. be correct)
  x⊗[y⊗z] : Bifunctor (Product C C) C C
  x⊗[y⊗z] = ⊗ ∘F (idF ⁂ ⊗) ∘F assocˡ _ _ _

unitor-coherenceʳ : [ (A ⊗₀ unit) ⊗₀ unit ⇒ A ⊗₀ unit ]⟨ ρ⇒ ⊗₁ C.id ≈ ρ⇒ ⟩
unitor-coherenceʳ = cancel-fromˡ unitorʳ unitorʳ-commute-from

unitor-coherenceˡ : [ unit ⊗₀ unit ⊗₀ A ⇒ unit ⊗₀ A ]⟨ C.id ⊗₁ λ⇒ ≈ λ⇒ ⟩
unitor-coherenceˡ = cancel-fromˡ unitorˡ unitorˡ-commute-from

-- All the implicits below can be inferred, but being explicit is clearer
unitorˡ-naturalIsomorphism : NaturalIsomorphism (unit ⊗-) idF
unitorˡ-naturalIsomorphism = record
  { F⇒G = ntHelper record
    { η       = λ X → λ⇒ {X}
    ; commute = λ f → unitorˡ-commute-from {f = f}
    }
  ; F⇐G = ntHelper record
    { η       = λ X → λ⇐ {X}
    ; commute = λ f → unitorˡ-commute-to {f = f}
    }
  ; iso = λ X →  unitorˡ.iso {X}
  }

unitorʳ-naturalIsomorphism : NaturalIsomorphism (-⊗ unit) idF
unitorʳ-naturalIsomorphism = record
  { F⇒G = ntHelper record
    { η       = λ X → ρ⇒ {X}
    ; commute = λ f → unitorʳ-commute-from {f = f}
    }
  ; F⇐G = ntHelper record
    { η       = λ X → ρ⇐ {X}
    ; commute = λ f → unitorʳ-commute-to {f = f}
    }
  ; iso = λ X → unitorʳ.iso {X}
  }

-- skipping the explicit arguments here, it does not increase understandability
associator-naturalIsomorphism : NaturalIsomorphism [x⊗y]⊗z x⊗[y⊗z]
associator-naturalIsomorphism = record
  { F⇒G = ntHelper record
    { η       = λ { ((X , Y) , Z) → α⇒ {X} {Y} {Z}}
    ; commute = λ _ → assoc-commute-from
    }
  ; F⇐G = ntHelper record
    { η       = λ _ → α⇐
    ; commute = λ _ → assoc-commute-to
    }
  ; iso = λ _ → associator.iso
  }

module unitorˡ-natural = NaturalIsomorphism unitorˡ-naturalIsomorphism
module unitorʳ-natural = NaturalIsomorphism unitorʳ-naturalIsomorphism
module associator-natural = NaturalIsomorphism associator-naturalIsomorphism

infixr 10 _⊗ᵢ_

_⊗ᵢ_ : X ≅ Y → Z ≅ W → X ⊗₀ Z ≅ Y ⊗₀ W
f ⊗ᵢ g = [ ⊗ ]-resp-≅ record
  { from = from f , from g
  ; to   = to f , to g
  ; iso  = record
    { isoˡ = isoˡ f , isoˡ g
    ; isoʳ = isoʳ f , isoʳ g
    }
  }

triangle-iso : idᵢ ⊗ᵢ unitorˡ ∘ᵢ associator ≈ᵢ unitorʳ {X} ⊗ᵢ idᵢ {Y}
triangle-iso = ⌞ triangle ⌟

triangle-inv : α⇐ ∘ id ⊗₁ λ⇐ ≈ ρ⇐ {X} ⊗₁ id {Y}
triangle-inv = to-≈ triangle-iso

pentagon-iso :
     idᵢ ⊗ᵢ associator ∘ᵢ associator ∘ᵢ associator {X} {Y} {Z} ⊗ᵢ idᵢ {W}
  ≈ᵢ associator ∘ᵢ associator
pentagon-iso = ⌞ pentagon ⌟

pentagon-inv : (α⇐ {X} {Y} {Z} ⊗₁ id {W} ∘ α⇐) ∘ id ⊗₁ α⇐ ≈ α⇐ ∘ α⇐
pentagon-inv = to-≈ pentagon-iso

refl⊗refl≃refl : idᵢ {A} ⊗ᵢ idᵢ {B} ≈ᵢ idᵢ
refl⊗refl≃refl = ⌞ ⊗.identity ⌟

Obj-⊗-Monoid : Monoid o (ℓ ⊔ e)
Obj-⊗-Monoid = record
  { Carrier = Obj
  ; _≈_ = _≅_
  ; _∙_ = _⊗₀_
  ; ε   = unit
  ; isMonoid = record
    { isSemigroup = record
      { assoc = λ x y z → associator {x} {y} {z}
      ; isMagma = record
        { isEquivalence = Morphism.≅-isEquivalence
        ; ∙-cong = _⊗ᵢ_
        }
      }
    ; identity = (λ x → unitorˡ {x}) , (λ x → unitorʳ {x})
    }
  }
