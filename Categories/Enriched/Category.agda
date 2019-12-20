{-# OPTIONS --without-K --safe #-}

-- Enriched category over a Monoidal category K

open import Categories.Category
  using (categoryHelper) renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Enriched.Category {o ℓ e} {K : Setoid-Category o ℓ e}
                                    (M : Monoidal K) where

open import Level
open import Function using (_$_)

open import Categories.Category.Monoidal.Properties M
  using (module Serialize; module Kelly's)
open import Categories.Functor using (Functor)
import Categories.Morphism.Reasoning K as MorphismReasoning
import Categories.Morphism.IsoEquiv K as IsoEquiv

open Setoid-Category K renaming (Obj to ObjK; id to idK)
open Monoidal M

record Category v : Set (o ⊔ ℓ ⊔ e ⊔ suc v) where
  open Commutation
  field
    Obj : Set v
    hom : (A B : Obj)   → ObjK
    id  : {A : Obj}     → unit ⇒ hom A A
    ⊚   : {A B C : Obj} → hom B C ⊗₀ hom A B ⇒ hom A C

    ⊚-assoc : {A B C D : Obj} →
      [ (hom C D ⊗₀ hom B C) ⊗₀ hom A B ⇒ hom A D ]⟨
        ⊚ ⊗₁ idK          ⇒⟨ hom B D ⊗₀ hom A B ⟩
        ⊚
      ≈ associator.from   ⇒⟨ hom C D ⊗₀ (hom B C ⊗₀ hom A B) ⟩
        idK ⊗₁ ⊚          ⇒⟨ hom C D ⊗₀ hom A C ⟩
        ⊚
      ⟩
    unitˡ : {A B : Obj} →
      [ unit ⊗₀ hom A B ⇒ hom A B ]⟨
        id ⊗₁ idK         ⇒⟨ hom B B ⊗₀ hom A B ⟩
        ⊚
      ≈ unitorˡ.from
      ⟩
    unitʳ : {A B : Obj} →
      [ hom A B ⊗₀ unit ⇒ hom A B ]⟨
        idK ⊗₁ id         ⇒⟨ hom A B ⊗₀ hom A A ⟩
        ⊚
      ≈ unitorʳ.from
      ⟩

-- The usual shorthand for hom-objects of an arbitrary category.

infix 15 _[_,_]

_[_,_] : ∀ {c} (C : Category c) (X Y : Category.Obj C) → ObjK
_[_,_] = Category.hom


-- A K-category C does not have morphisms of its own, but the
-- collection of K-morphisms from the monoidal unit into the
-- hom-objects of C forms a setoid.  This induces the *underlying*
-- category of C.

underlying : ∀ {c} (C : Category c) → Setoid-Category c ℓ e
underlying C = categoryHelper (record
  { Obj = Obj
  ; _⇒_ = λ A B → unit ⇒ hom A B
  ; _≈_ = λ f g → f ≈ g
  ; id  = id
  ; _∘_ = λ f g → ⊚ ∘ f ⊗₁ g ∘ unitorˡ.to
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} →
    begin
      ⊚ ∘ (⊚ ∘ h ⊗₁ g ∘ unitorˡ.to) ⊗₁ f ∘ unitorˡ.to
    ≈⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
      ⊚ ∘ ⊚ ⊗₁ idK ∘ (h ⊗₁ g ∘ unitorˡ.to) ⊗₁ f ∘ unitorˡ.to
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ʳ ⟩
      ⊚ ∘ ⊚ ⊗₁ idK ∘ ((h ⊗₁ g) ⊗₁ f) ∘ (unitorˡ.to ⊗₁ idK) ∘ unitorˡ.to
    ≈⟨ pullˡ ⊚-assoc ⟩
      (⊚ ∘ idK ⊗₁ ⊚ ∘ associator.from) ∘ ((h ⊗₁ g) ⊗₁ f) ∘
        (unitorˡ.to ⊗₁ idK) ∘ unitorˡ.to
    ≈˘⟨ pushˡ (assoc ⟩∘⟨refl) ⟩
      (((⊚ ∘ idK ⊗₁ ⊚) ∘ associator.from) ∘ (h ⊗₁ g) ⊗₁ f) ∘
        (unitorˡ.to ⊗₁ idK) ∘ unitorˡ.to
    ≈⟨ pullʳ assoc-commute-from ⟩∘⟨refl ⟩
      ((⊚ ∘ idK ⊗₁ ⊚) ∘ (h ⊗₁ (g ⊗₁ f)) ∘ associator.from) ∘
        (unitorˡ.to ⊗₁ idK) ∘ unitorˡ.to
    ≈˘⟨ assoc ⟩∘⟨ to-≈ Kelly's.coherence-iso₁ ⟩∘⟨refl ⟩
      (((⊚ ∘ idK ⊗₁ ⊚) ∘ h ⊗₁ (g ⊗₁ f)) ∘ associator.from) ∘
        (associator.to ∘ unitorˡ.to) ∘ unitorˡ.to
    ≈⟨ pullˡ (cancelInner associator.isoʳ) ⟩
      (((⊚ ∘ idK ⊗₁ ⊚) ∘ h ⊗₁ (g ⊗₁ f)) ∘ unitorˡ.to) ∘ unitorˡ.to
    ≈⟨ pullʳ unitorˡ-commute-to ⟩
      ((⊚ ∘ idK ⊗₁ ⊚) ∘ h ⊗₁ (g ⊗₁ f)) ∘ idK ⊗₁ unitorˡ.to ∘ unitorˡ.to
    ≈˘⟨ pushʳ split₂ˡ ⟩∘⟨refl ⟩
      (⊚ ∘ h ⊗₁ (⊚ ∘ g ⊗₁ f)) ∘ idK ⊗₁ unitorˡ.to ∘ unitorˡ.to
    ≈˘⟨ pushʳ (pushˡ split₂ʳ) ⟩
      ⊚ ∘ h ⊗₁ ((⊚ ∘ g ⊗₁ f) ∘ unitorˡ.to) ∘ unitorˡ.to
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩∘⟨refl ⟩
      ⊚ ∘ h ⊗₁ (⊚ ∘ g ⊗₁ f ∘ unitorˡ.to) ∘ unitorˡ.to
    ∎
  ; identityˡ = λ {_} {_} {f} → begin
      ⊚ ∘ id ⊗₁ f ∘ unitorˡ.to
    ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩∘⟨refl ⟩
      ⊚ ∘ (id ⊗₁ idK ∘ idK ⊗₁ f) ∘ unitorˡ.to
    ≈˘⟨ refl⟩∘⟨ pushʳ unitorˡ-commute-to ⟩
      ⊚ ∘ id ⊗₁ idK ∘ unitorˡ.to ∘ f
    ≈⟨ pullˡ unitˡ ⟩
      unitorˡ.from ∘ unitorˡ.to ∘ f
    ≈⟨ cancelˡ unitorˡ.isoʳ ⟩
      f
    ∎
  ; identityʳ = λ {_} {_} {f} → begin
      ⊚ ∘ f ⊗₁ id ∘ unitorˡ.to
    ≈⟨ refl⟩∘⟨ serialize₂₁ ⟩∘⟨refl ⟩
      ⊚ ∘ (idK ⊗₁ id ∘ f ⊗₁ idK) ∘ unitorˡ.to
    ≈⟨ pullˡ (pullˡ unitʳ) ⟩
      (unitorʳ.from ∘ f ⊗₁ idK) ∘ unitorˡ.to
    ≈⟨ unitorʳ-commute-from ⟩∘⟨refl ⟩
      (f ∘ unitorʳ.from) ∘ unitorˡ.to
    ≈˘⟨ (refl⟩∘⟨ Kelly's.coherence₃) ⟩∘⟨refl ⟩
      (f ∘ unitorˡ.from) ∘ unitorˡ.to
    ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
      f
    ∎
  ; equiv    = equiv
  ; ∘-resp-≈ = λ eq₁ eq₂ → ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ⊗-resp-≈ eq₁ eq₂
  })
  where
    open Category C
    open MonoidalReasoning
    open MorphismReasoning
    open IsoEquiv._≃_
    open Serialize

module Underlying {c} (C : Category c) = Setoid-Category (underlying C)
