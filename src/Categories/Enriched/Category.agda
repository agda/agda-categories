{-# OPTIONS --without-K --safe #-}

-- Enriched category over a Monoidal category V

open import Categories.Category using (module Commutation) renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Enriched.Category {o ℓ e} {V : Setoid-Category o ℓ e}
                                    (M : Monoidal V) where

open import Level

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)
open import Categories.Morphism.Reasoning V using (pullˡ; pullʳ; pushˡ)

open Setoid-Category V renaming (Obj to ObjV; id to idV)
  using (_⇒_; _∘_)
open Commutation V
open Monoidal M using (unit; _⊗₀_; _⊗₁_; module associator; module unitorˡ;
  module unitorʳ; assoc-commute-from)
open Shorthands

record Category (v : Level) : Set (o ⊔ ℓ ⊔ e ⊔ suc v) where
  field
    Obj : Set v
    hom : (A B : Obj)   → ObjV
    id  : {A : Obj}     → unit ⇒ hom A A
    ⊚   : {A B C : Obj} → hom B C ⊗₀ hom A B ⇒ hom A C

    ⊚-assoc : {A B C D : Obj} →
      [ (hom C D ⊗₀ hom B C) ⊗₀ hom A B ⇒ hom A D ]⟨
        ⊚ ⊗₁ idV          ⇒⟨ hom B D ⊗₀ hom A B ⟩
        ⊚
      ≈ associator.from   ⇒⟨ hom C D ⊗₀ (hom B C ⊗₀ hom A B) ⟩
        idV ⊗₁ ⊚          ⇒⟨ hom C D ⊗₀ hom A C ⟩
        ⊚
      ⟩
    unitˡ : {A B : Obj} →
      [ unit ⊗₀ hom A B ⇒ hom A B ]⟨
        id ⊗₁ idV         ⇒⟨ hom B B ⊗₀ hom A B ⟩
        ⊚
      ≈ unitorˡ.from
      ⟩
    unitʳ : {A B : Obj} →
      [ hom A B ⊗₀ unit ⇒ hom A B ]⟨
        idV ⊗₁ id         ⇒⟨ hom A B ⊗₀ hom A A ⟩
        ⊚
      ≈ unitorʳ.from
      ⟩

  -- A version of ⊚-assoc using generalized hom-variables.
  --
  -- In this version of associativity, the generalized variables f, g
  -- and h represent V-morphisms, or rather, morphism-valued maps,
  -- such as V-natural transformations or V-functorial actions.  This
  -- version is therefore well-suited for proving derived equations,
  -- such as functorial laws or commuting diagrams, that involve such
  -- maps.  For examples, see Underlying.assoc below, or the modules
  -- Enriched.Functor and Enriched.NaturalTransformation.

  ⊚-assoc-var : {X Y Z : ObjV} {A B C D : Obj}
                {f : X ⇒ hom C D} {g : Y ⇒ hom B C} {h : Z ⇒ hom A B} →
      [ (X ⊗₀ Y) ⊗₀ Z ⇒ hom A D ]⟨
        (⊚ ∘ f ⊗₁ g) ⊗₁ h  ⇒⟨ hom B D ⊗₀ hom A B ⟩
        ⊚
      ≈ associator.from    ⇒⟨ X ⊗₀ (Y ⊗₀ Z) ⟩
        f ⊗₁ (⊚ ∘ g ⊗₁ h)  ⇒⟨ hom C D ⊗₀ hom A C ⟩
        ⊚
      ⟩
  ⊚-assoc-var {f = f} {g} {h} = begin
    ⊚ ∘ (⊚ ∘ f ⊗₁ g) ⊗₁ h                 ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    ⊚ ∘ ⊚ ⊗₁ idV ∘ (f ⊗₁ g) ⊗₁ h          ≈⟨ pullˡ ⊚-assoc ⟩
    (⊚ ∘ idV ⊗₁ ⊚ ∘ α⇒) ∘ (f ⊗₁ g) ⊗₁ h   ≈⟨ pullʳ (pullʳ assoc-commute-from) ⟩
    ⊚ ∘ idV ⊗₁ ⊚ ∘ f ⊗₁ (g ⊗₁ h) ∘ α⇒     ≈˘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    ⊚ ∘ f ⊗₁ (⊚ ∘ g ⊗₁ h) ∘ α⇒            ∎

-- The usual shorthand for hom-objects of an arbitrary category.

infix 15 _[_,_]

_[_,_] : ∀ {c} (C : Category c) (X Y : Category.Obj C) → ObjV
_[_,_] = Category.hom
