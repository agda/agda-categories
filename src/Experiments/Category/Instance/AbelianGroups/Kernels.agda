{-# OPTIONS --without-K --safe #-}

-- Proofs about the kernels of abelian groups
module Experiments.Category.Instance.AbelianGroups.Kernels where

open import Level
open import Function using (_$_)

open import Data.Unit.Polymorphic
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)

import Algebra.Construct.DirectProduct as DirectProduct
open import Algebra.Properties.AbelianGroup

import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Category.Core
open import Categories.Object.Zero
open import Categories.Object.Kernel
open import Categories.Object.Cokernel

open import Categories.Morphism.Notation
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

open import Categories.Category.Preadditive
open import Categories.Category.Additive
open import Experiments.Category.PreAbelian

open import Experiments.Category.Instance.AbelianGroups
open import Experiments.Category.Instance.AbelianGroups.Preadditive
open import Experiments.Category.Instance.AbelianGroups.Additive

private
  variable
    c ℓ : Level

open AbelianGroup
open AbelianGroupHomomorphism

-- The category of abelian groups has all kernels
kernels : ∀ {A B : AbelianGroup (c ⊔ ℓ) ℓ} (f : AbelianGroupHomomorphism A B) → Kernel 𝟎 f
kernels {A = A} {B = B} f = record
  { kernel = subgroup A P ∙-closed ε-closed ⁻¹-closed
 ; kernel⇒ = record
    { ⟦_⟧ = proj₁
    ; cong = λ eq → eq
    ; homo = λ _ _ → A.refl
    }
  ; isKernel = record
    { commute = proj₂
    ; universal = λ {X} {h} eq → record
      { ⟦_⟧ = λ x → (⟦ h ⟧ x) , (eq x)
      ; cong = cong h
      ; homo = homo h
      }
    ; factors = λ _ → A.refl
    ; unique = λ eq x → A.sym (eq x)
    }
  }
  where
    module A = AbelianGroup A
    module B = AbelianGroup B

    open SR B.setoid

    P : A.Carrier → Set _
    P x = ⟦ f ⟧ x B.≈ B.ε

    ∙-closed : ∀ x y → P x → P y → P (x A.∙ y)
    ∙-closed x y px py = begin
      ⟦ f ⟧ (x A.∙ y)     ≈⟨ homo f x y ⟩
      ⟦ f ⟧ x B.∙ ⟦ f ⟧ y ≈⟨ B.∙-cong px py ⟩
      B.ε B.∙ B.ε         ≈⟨ B.identityˡ B.ε ⟩
      B.ε ∎

    ε-closed : P A.ε
    ε-closed = ε-homo f

    ⁻¹-closed : ∀ x → P x → P (x A.⁻¹)
    ⁻¹-closed x px = begin
      ⟦ f ⟧ (x A.⁻¹) ≈⟨ ⁻¹-homo f x ⟩
      ⟦ f ⟧ x B.⁻¹   ≈⟨ B.⁻¹-cong px  ⟩
      B.ε B.⁻¹       ≈⟨ ε⁻¹≈ε B ⟩
      B.ε ∎
