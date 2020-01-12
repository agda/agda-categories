{-# OPTIONS --without-K --safe #-}

-- Enriched category over a Monoidal category V

open import Categories.Category
  using (categoryHelper) renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Enriched.Category {o ℓ e} {V : Setoid-Category o ℓ e}
                                    (M : Monoidal V) where

open import Level
open import Function using (_$_)

open import Categories.Category.Monoidal.Properties M using (module Kelly's)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)
open import Categories.Functor using (Functor)
open import Categories.Morphism.Reasoning V
import Categories.Morphism.IsoEquiv V as IsoEquiv

open Setoid-Category V renaming (Obj to ObjV; id to idV)
open Commutation
open Monoidal M
open Shorthands
open IsoEquiv._≃_

record Category v : Set (o ⊔ ℓ ⊔ e ⊔ suc v) where
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
  -- such as V-natural transofrmations or V-functorial actions.  This
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

-- A V-category C does not have morphisms of its own, but the
-- collection of V-morphisms from the monoidal unit into the
-- hom-objects of C forms a setoid.  This induces the *underlying*
-- category of C.

Underlying : ∀ {c} (C : Category c) → Setoid-Category c ℓ e
Underlying C = categoryHelper (record
  { Obj = Obj
  ; _⇒_ = λ A B → unit ⇒ hom A B
  ; _≈_ = λ f g → f ≈ g
  ; id  = id
  ; _∘_ = λ f g → ⊚ ∘ f ⊗₁ g ∘ λ⇐
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} →
    begin
      ⊚ ∘ (⊚ ∘ h ⊗₁ g ∘ λ⇐) ⊗₁ f ∘ λ⇐
    ≈˘⟨ refl⟩∘⟨ assoc ⟩⊗⟨refl ⟩∘⟨refl ⟩
      ⊚ ∘ ((⊚ ∘ h ⊗₁ g) ∘ λ⇐) ⊗₁ f ∘ λ⇐
    ≈⟨ refl⟩∘⟨ pushˡ split₁ʳ ⟩
      ⊚ ∘ (⊚ ∘ h ⊗₁ g) ⊗₁ f ∘ (λ⇐ ⊗₁ idV) ∘ λ⇐
    ≈⟨ pullˡ ⊚-assoc-var ⟩
      (⊚ ∘ h ⊗₁ (⊚ ∘ g ⊗₁ f) ∘ α⇒) ∘ (λ⇐ ⊗₁ idV) ∘ λ⇐
    ≈˘⟨ pushˡ (pushʳ (pushʳ
          (switch-tofromˡ associator (to-≈ Kelly's.coherence-iso₁)))) ⟩
      (⊚ ∘ h ⊗₁ (⊚ ∘ g ⊗₁ f) ∘ λ⇐) ∘ λ⇐
    ≈⟨ pullʳ (pullʳ unitorˡ-commute-to) ⟩
      ⊚ ∘ h ⊗₁ (⊚ ∘ g ⊗₁ f) ∘ idV ⊗₁ λ⇐ ∘ λ⇐
    ≈˘⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
      ⊚ ∘ h ⊗₁ ((⊚ ∘ g ⊗₁ f) ∘ λ⇐) ∘ λ⇐
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩∘⟨refl ⟩
      ⊚ ∘ h ⊗₁ (⊚ ∘ g ⊗₁ f ∘ λ⇐) ∘ λ⇐
    ∎
  ; identityˡ = λ {_} {_} {f} → begin
      ⊚ ∘ id ⊗₁ f ∘ λ⇐                 ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩∘⟨refl ⟩
      ⊚ ∘ (id ⊗₁ idV ∘ idV ⊗₁ f) ∘ λ⇐  ≈˘⟨ refl⟩∘⟨ pushʳ unitorˡ-commute-to ⟩
      ⊚ ∘ id ⊗₁ idV ∘ λ⇐ ∘ f           ≈⟨ pullˡ unitˡ ⟩
      λ⇒ ∘ λ⇐ ∘ f                      ≈⟨ cancelˡ unitorˡ.isoʳ ⟩
      f                                ∎
  ; identityʳ = λ {_} {_} {f} → begin
      ⊚ ∘ f ⊗₁ id ∘ λ⇐                 ≈⟨ refl⟩∘⟨ serialize₂₁ ⟩∘⟨refl ⟩
      ⊚ ∘ (idV ⊗₁ id ∘ f ⊗₁ idV) ∘ λ⇐  ≈⟨ pullˡ (pullˡ unitʳ) ⟩
      (unitorʳ.from ∘ f ⊗₁ idV) ∘ λ⇐   ≈⟨ unitorʳ-commute-from ⟩∘⟨refl ⟩
      (f ∘ unitorʳ.from) ∘ λ⇐          ≈˘⟨ (refl⟩∘⟨ Kelly's.coherence₃) ⟩∘⟨refl ⟩
      (f ∘ λ⇒) ∘ λ⇐                    ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
      f                                ∎
  ; equiv    = equiv
  ; ∘-resp-≈ = λ eq₁ eq₂ → ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ⊗-resp-≈ eq₁ eq₂
  })
  where open Category C

module Underlying {c} (C : Category c) = Setoid-Category (Underlying C)
