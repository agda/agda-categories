{-# OPTIONS --without-K --safe #-}
module Experiments.Category.Instance.AbelianGroups.Preadditive where

open import Level
open import Data.Unit.Polymorphic
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)

import Algebra.Construct.DirectProduct as DirectProduct
open import Algebra.Properties.AbelianGroup

import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Object.Zero
open import Categories.Object.Biproduct

import Categories.Morphism.Reasoning as MR

open import Experiments.Category.Instance.AbelianGroups
open import Categories.Category.Preadditive

private
  variable
    c ℓ : Level

open AbelianGroup
open AbelianGroupHomomorphism

AbelianGroupsPreadditive : Preadditive (AbelianGroups c ℓ)
AbelianGroupsPreadditive = record
  { _+_ = λ {G} {H} f g →
    let open SR (setoid H)
        open MR (Delooping H)
    in record
      { ⟦_⟧ = λ x → H [ ⟦ f ⟧ x ∙ ⟦ g ⟧ x ]
      ; cong = λ eq → ∙-cong H (cong f eq) (cong g eq)
      ; homo = λ x y → begin
        H [ ⟦ f ⟧ (G [ x ∙ y ]) ∙ ⟦ g ⟧ (G [ x ∙ y ]) ]         ≈⟨ ∙-cong H (homo f x y) (homo g x y) ⟩
        H [ H [ ⟦ f ⟧ x ∙ ⟦ f ⟧ y ] ∙ H [ ⟦ g ⟧ x ∙ ⟦ g ⟧ y ] ] ≈⟨ center (comm H (⟦ f ⟧ y) (⟦ g ⟧ x)) ⟩
        H [ ⟦ f ⟧ x ∙ H [ H [ ⟦ g ⟧ x ∙ ⟦ f ⟧ y ] ∙ ⟦ g ⟧ y ] ] ≈⟨ pull-first (refl H) ⟩
        H [ H [ ⟦ f ⟧ x ∙ ⟦ g ⟧ x ] ∙ H [ ⟦ f ⟧ y ∙ ⟦ g ⟧ y ] ] ∎
      }
  ; 0H = λ {G} {H} → record
    { ⟦_⟧ = λ _ → ε H
    ; cong = λ _ → refl H
    ; homo = λ _ _ → sym H (identityʳ H _)
    }
  ; -_ = λ {G} {H} f →
    let open SR (setoid H)
    in record
      { ⟦_⟧ = λ x → H [ ⟦ f ⟧ x ⁻¹]
      ; cong = λ eq → ⁻¹-cong H (cong f eq)
      ; homo = λ x y → begin
        H [ ⟦ f ⟧ (G [ x ∙ y ]) ⁻¹]             ≈⟨ ⁻¹-cong H (homo f x y) ⟩
        H [ H [ ⟦ f ⟧ x ∙ ⟦ f ⟧ y ] ⁻¹]         ≈⟨ ⁻¹-distrib-∙ H (⟦ f ⟧ x) (⟦ f ⟧ y) ⟩
        H [ H [ ⟦ f ⟧ x ⁻¹] ∙ H [ ⟦ f ⟧ y ⁻¹] ] ∎
      }
  ; HomIsAbGroup = λ A B → isAbGroupHelper record
    { isEquivalence = record
      { refl = λ x → refl B
      ; sym = λ eq x → sym B (eq x)
      ; trans = λ eq₁ eq₂ x → trans B (eq₁ x) (eq₂ x)
      }
    ; ∙-cong = λ eq₁ eq₂ x →  ∙-cong B (eq₁ x) (eq₂ x)
    ; ⁻¹-cong = λ eq x → ⁻¹-cong B (eq x)
    ; assoc = λ f g h x → assoc B (⟦ f ⟧ x) (⟦ g ⟧ x) (⟦ h ⟧ x)
    ; identityˡ = λ f x → identityˡ B (⟦ f ⟧ x)
    ; inverseˡ = λ f x → inverseˡ B (⟦ f ⟧ x)
    ; comm = λ f g x → comm B (⟦ f ⟧ x) (⟦ g ⟧ x)
    }
  ; +-resp-∘ = λ {A} {B} {C} {D} {f} {g} {h} {i} x → homo i (⟦ f ⟧ (⟦ h ⟧ x)) (⟦ g ⟧ (⟦ h ⟧ x))
  }

