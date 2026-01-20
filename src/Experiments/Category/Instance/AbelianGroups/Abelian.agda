{-# OPTIONS --without-K --safe #-}

module Experiments.Category.Instance.AbelianGroups.Abelian where

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

import Categories.Morphism as Mor
import Categories.Morphism.Normal as NormalMor
import Categories.Morphism.Reasoning as MR

open import Categories.Category.Preadditive
open import Categories.Category.Additive
open import Experiments.Category.PreAbelian
open import Experiments.Category.Abelian

open import Experiments.Category.Instance.AbelianGroups
open import Experiments.Category.Instance.AbelianGroups.Preadditive
open import Experiments.Category.Instance.AbelianGroups.Additive
open import Experiments.Category.Instance.AbelianGroups.Preabelian

private
  variable
    c ℓ : Level

open AbelianGroup
open AbelianGroupHomomorphism

module _ {c ℓ} {A K : AbelianGroup (c ⊔ ℓ) (c ⊔ ℓ)} where
  private
    module A = AbelianGroup A
    module K = AbelianGroup K

    open Mor (AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ))
    open NormalMor (AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ))

  mono-is-normal : ∀ {k : AbelianGroupHomomorphism K A} → Mono k → IsNormalMonomorphism 𝟎 k
  mono-is-normal {k = k} k-mono =
    let coker = cokernels {ℓ = c ⊔ ℓ} k
        open Zero (𝟎 {c = c ⊔ ℓ} {ℓ = c ⊔ ℓ})
        module coker = Cokernel coker
    in record
      { B = coker.cokernel
      ; arr = coker.cokernel⇒
      ; isKernel = record
        { commute = coker.commute
        ; universal = λ { {X} {h} eq →
          let module X = AbelianGroup X
              open SR A.setoid
              open MR (Delooping A)
          in record
            { ⟦_⟧ = λ x → proj₁ (eq (x X.⁻¹))
            ; cong = λ {x} {y} x≈y → mono-injective {c = c ⊔ ℓ} {ℓ = c ⊔ ℓ} k k-mono $ begin
              ⟦ k ⟧ (proj₁ (eq (x X.⁻¹)))                                              ≈⟨ insertˡ (A.inverseˡ (⟦ h ⟧ (x X.⁻¹))) ⟩
              ⟦ h ⟧ (x X.⁻¹) A.⁻¹ A.∙ (⟦ h ⟧ (x X.⁻¹) A.∙ ⟦ k ⟧ (proj₁ (eq (x X.⁻¹)))) ≈⟨ elimʳ (proj₂ (eq (x X.⁻¹))) ⟩
              ⟦ h ⟧ (x X.⁻¹) A.⁻¹                                                      ≈⟨ A.⁻¹-cong (cong h (X.⁻¹-cong x≈y)) ⟩
              ⟦ h ⟧ (y X.⁻¹) A.⁻¹                                                      ≈⟨ introʳ (proj₂ (eq (y X.⁻¹))) ⟩
              ⟦ h ⟧ (y X.⁻¹) A.⁻¹ A.∙ (⟦ h ⟧ (y X.⁻¹) A.∙ ⟦ k ⟧ (proj₁ (eq (y X.⁻¹)))) ≈⟨ cancelˡ (A.inverseˡ (⟦ h ⟧ (y X.⁻¹))) ⟩
              ⟦ k ⟧ (proj₁ (eq (y X.⁻¹))) ∎
            ; homo = λ x y → mono-injective {c = c ⊔ ℓ} {ℓ = c ⊔ ℓ} k k-mono $ begin
              ⟦ k ⟧ (proj₁ (eq ((x X.∙ y) X.⁻¹)))                                                              ≈⟨ insertˡ (A.inverseˡ (⟦ h ⟧ ((x X.∙ y) X.⁻¹))) ⟩
              ⟦ h ⟧ ((x X.∙ y) X.⁻¹) A.⁻¹ A.∙ (⟦ h ⟧ ((x X.∙ y) X.⁻¹) A.∙ ⟦ k ⟧ (proj₁ (eq ((x X.∙ y) X.⁻¹)))) ≈⟨ elimʳ (proj₂ (eq ((x X.∙ y) X.⁻¹))) ⟩
              ⟦ h ⟧ ((x X.∙ y) X.⁻¹) A.⁻¹                                                                      ≈⟨ A.⁻¹-cong (⁻¹-homo h (x X.∙ y)) ⟩
              (⟦ h ⟧ (x X.∙ y) A.⁻¹) A.⁻¹                                                                      ≈⟨ ⁻¹-involutive A (⟦ h ⟧ (x X.∙ y)) ⟩
              ⟦ h ⟧ (x X.∙ y)                                                                                  ≈⟨ homo h x y ⟩
              ⟦ h ⟧ x A.∙ ⟦ h ⟧ y                                                                              ≈⟨ introʳ (proj₂ (eq (y X.⁻¹))) ⟩
              ⟦ h ⟧ x A.∙ ⟦ h ⟧ y A.∙ (⟦ h ⟧ (y X.⁻¹) A.∙ ⟦ k ⟧ (proj₁ (eq (y X.⁻¹))))                         ≈⟨ cancelInner (A.trans (A.∙-congˡ (⁻¹-homo h y)) (A.inverseʳ (⟦ h ⟧ y))) ⟩
              ⟦ h ⟧ x A.∙ ⟦ k ⟧ (proj₁ (eq (y X.⁻¹)))                                                          ≈⟨ pushʳ (introˡ (proj₂ (eq (x X.⁻¹)))) ⟩
              ⟦ h ⟧ x A.∙ (⟦ h ⟧ (x X.⁻¹) A.∙ ⟦ k ⟧ (proj₁ (eq (x X.⁻¹)))) A.∙ ⟦ k ⟧ (proj₁ (eq (y X.⁻¹)))     ≈⟨ A.∙-congʳ (cancelˡ (A.trans (A.∙-congˡ (⁻¹-homo h x)) (A.inverseʳ (⟦ h ⟧ x)))) ⟩
              ⟦ k ⟧ (proj₁ (eq (x X.⁻¹))) A.∙ ⟦ k ⟧ (proj₁ (eq (y X.⁻¹)))                                      ≈˘⟨ homo k (proj₁ (eq (x X.⁻¹))) (proj₁ (eq (y X.⁻¹))) ⟩
              ⟦ k ⟧ (proj₁ (eq (x X.⁻¹)) K.∙ proj₁ (eq (y X.⁻¹))) ∎
            }}
        ; factors = λ {X} {h} {eq} x →
          let module X = AbelianGroup X
              open SR A.setoid
              open MR (Delooping A)
          in begin
            ⟦ h ⟧ x                                                      ≈⟨ insertˡ (proj₂ (eq (x X.⁻¹))) ⟩
            ⟦ h ⟧ (x X.⁻¹) A.∙ (⟦ k ⟧ (proj₁ (eq (x X.⁻¹))) A.∙ ⟦ h ⟧ x) ≈⟨ A.∙-cong (⁻¹-homo h x) (A.comm (⟦ k ⟧ (proj₁ (eq (x X.⁻¹)))) (⟦ h ⟧ x)) ⟩
            ⟦ h ⟧ x A.⁻¹ A.∙ (⟦ h ⟧ x A.∙ ⟦ k ⟧ (proj₁ (eq (x X.⁻¹))))   ≈⟨ cancelˡ (A.inverseˡ (⟦ h ⟧ x)) ⟩
            ⟦ k ⟧ (proj₁ (eq (x X.⁻¹))) ∎
        ; unique = λ {X} {h} {i} {eq} eq-hki x →
          let module X = AbelianGroup X
              open SR A.setoid
              open MR (Delooping A)
          -- FIXME: This is factors, so factor (ayoooo) this out
          in mono-injective {c = c ⊔ ℓ} {ℓ = c ⊔ ℓ} k k-mono $ begin
            ⟦ k ⟧ (⟦ i ⟧ x)                                              ≈˘⟨ eq-hki x ⟩
            ⟦ h ⟧ x                                                      ≈⟨ insertˡ (proj₂ (eq (x X.⁻¹))) ⟩
            ⟦ h ⟧ (x X.⁻¹) A.∙ (⟦ k ⟧ (proj₁ (eq (x X.⁻¹))) A.∙ ⟦ h ⟧ x) ≈⟨ A.∙-cong (⁻¹-homo h x) (A.comm (⟦ k ⟧ (proj₁ (eq (x X.⁻¹)))) (⟦ h ⟧ x)) ⟩
            ⟦ h ⟧ x A.⁻¹ A.∙ (⟦ h ⟧ x A.∙ ⟦ k ⟧ (proj₁ (eq (x X.⁻¹))))   ≈⟨ cancelˡ (A.inverseˡ (⟦ h ⟧ x)) ⟩
            ⟦ k ⟧ (proj₁ (eq (x X.⁻¹))) ∎
        }
      }

  epi-is-normal : ∀ {k : AbelianGroupHomomorphism A K} → Epi k → IsNormalEpimorphism 𝟎 k
  epi-is-normal {k = k} k-epi =
    let ker = kernels {c = c ⊔ ℓ} k
        open Zero (𝟎 {c = c ⊔ ℓ} {ℓ = c ⊔ ℓ})
        module ker = Kernel ker
    in record
      { arr = ker.kernel⇒
      ; isCokernel = record
        { commute = ker.commute
        ; universal = λ {X} {h} eq →
          let module X = AbelianGroup X
              open SR X.setoid
              -- Pick an element out of the preimage
              preimage = λ x → proj₁ (epi-surjective {c = c} {ℓ = ℓ} k k-epi x)
              preimage-eq = λ x → proj₂ (epi-surjective {c = c} {ℓ = ℓ} k k-epi x)
          in record
            { ⟦_⟧ = λ x → ⟦ h ⟧ (preimage x)
            ; cong = λ {x} {y} x≈y → cong h {!!}
            -- begin
              -- ⟦ h ⟧ (proj₁ (epi-surjective {c = c} {ℓ = ℓ} k k-epi x)) ≈⟨ {! eq (? , ?)!} ⟩
              -- {!!} ≈⟨ {!!} ⟩
              -- ⟦ h ⟧ (proj₁ (epi-surjective {c = c} {ℓ = ℓ} k k-epi y)) ∎
            ; homo = {!!}
            }
        ; factors = {!!}
        ; unique = {!!}
        }
      }

AbelianGroupsAbelian : Abelian (AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ))
AbelianGroupsAbelian {c = c} {ℓ = ℓ} = record
  { preAbelian = AbelianGroupsPreAbelian {c = c} {ℓ = ℓ}
  ; mono-is-normal = mono-is-normal {c = c} {ℓ = ℓ}
  ; epi-is-normal = {!!}
  }
