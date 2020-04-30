{-# OPTIONS --without-K --safe #-}
-- The Underlying category of an Enriched category over a Monoidal category V
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Core renaming (Category to Setoid-Category)

module Categories.Enriched.Category.Underlying {o ℓ e} {V : Setoid-Category o ℓ e}
                                    (M : Monoidal V) where

open import Level
open import Function using (_$_)

open import Categories.Enriched.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal.Properties M using (module Kelly's)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)
open import Categories.Morphism.Reasoning V
import Categories.Morphism.IsoEquiv V as IsoEquiv

open Setoid-Category V renaming (Obj to ObjV; id to idV)
open Monoidal M
open Shorthands
open IsoEquiv._≃_

-- A V-category C does not have morphisms of its own, but the
-- collection of V-morphisms from the monoidal unit into the
-- hom-objects of C forms a setoid.  This induces the *underlying*
-- category of C.

Underlying : {c : Level} (C : Category M c) → Setoid-Category c ℓ e
Underlying C = categoryHelper (record
  { Obj = Obj
  ; _⇒_ = λ A B → unit ⇒ hom A B
  ; _≈_ = λ f g → f ≈ g
  ; id  = id
  ; _∘_ = λ f g → ⊚ ∘ f ⊗₁ g ∘ λ⇐
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} →
    begin
      ⊚ ∘ (⊚ ∘ h ⊗₁ g ∘ λ⇐) ⊗₁ f ∘ λ⇐                 ≈˘⟨ refl⟩∘⟨ assoc ⟩⊗⟨refl ⟩∘⟨refl ⟩
      ⊚ ∘ ((⊚ ∘ h ⊗₁ g) ∘ λ⇐) ⊗₁ f ∘ λ⇐                ≈⟨ refl⟩∘⟨ pushˡ split₁ʳ ⟩
      ⊚ ∘ (⊚ ∘ h ⊗₁ g) ⊗₁ f ∘ (λ⇐ ⊗₁ idV) ∘ λ⇐        ≈⟨ pullˡ ⊚-assoc-var ⟩
      (⊚ ∘ h ⊗₁ (⊚ ∘ g ⊗₁ f) ∘ α⇒) ∘ (λ⇐ ⊗₁ idV) ∘ λ⇐ ≈˘⟨ pushˡ (pushʳ (pushʳ
                                                            (switch-tofromˡ associator (to-≈ Kelly's.coherence-iso₁)))) ⟩
      (⊚ ∘ h ⊗₁ (⊚ ∘ g ⊗₁ f) ∘ λ⇐) ∘ λ⇐                ≈⟨ pullʳ (pullʳ unitorˡ-commute-to) ⟩
      ⊚ ∘ h ⊗₁ (⊚ ∘ g ⊗₁ f) ∘ idV ⊗₁ λ⇐ ∘ λ⇐           ≈˘⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
      ⊚ ∘ h ⊗₁ ((⊚ ∘ g ⊗₁ f) ∘ λ⇐) ∘ λ⇐                ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩∘⟨refl ⟩
      ⊚ ∘ h ⊗₁ (⊚ ∘ g ⊗₁ f ∘ λ⇐) ∘ λ⇐
    ∎
  ; identityˡ = λ {_} {_} {f} → begin
      ⊚ ∘ id ⊗₁ f ∘ λ⇐                 ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩∘⟨refl ⟩
      ⊚ ∘ (id ⊗₁ idV ∘ idV ⊗₁ f) ∘ λ⇐  ≈˘⟨ refl⟩∘⟨ pushʳ unitorˡ-commute-to ⟩
      ⊚ ∘ id ⊗₁ idV ∘ λ⇐ ∘ f           ≈⟨ pullˡ unitˡ ⟩
      λ⇒ ∘ λ⇐ ∘ f                       ≈⟨ cancelˡ unitorˡ.isoʳ ⟩
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

module Underlying {c} (C : Category M c) = Setoid-Category (Underlying C)
