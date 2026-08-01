{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Symmetry of the tensor product of enriched categories.

module Categories.Enriched.Functor.TensorProduct.Symmetric
  {o ℓ e} {V : Category o ℓ e} {M : Monoidal V} (S : Symmetric M) where

open import Data.Product using (_,_; swap)

import Categories.Enriched.Category as Enriched
import Categories.Enriched.Category.Opposite as Opposite
import Categories.Category.Monoidal.Interchange.Braided as BraidedInterchange
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open Category V
open Monoidal M
open Symmetric S using (braided)
open BraidedInterchange braided using (module swapInner)
  renaming (hasInterchange to interchange)
open import Categories.Category.Monoidal.Interchange using (HasInterchange)
open HasInterchange interchange using ()
  renaming (natural to interchange-natural)
open import Categories.Category.Monoidal.Braided.Properties braided
  using (braiding-coherence-σ)
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Properties M using (coherence-inv₃)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Enriched.Category M using (_[_,_])
open import Categories.Enriched.Category.TensorProduct interchange using (_⊠_)
open import Categories.Enriched.Functor M using (Functor; _∘F_)
open import Categories.Morphism.Reasoning V
open import Categories.Category.Monoidal.Interchange.Symmetric S
  using (swapInner-braiding′; swapInner-braidingʳ; swapInner-unitˡ⁻¹)
open BraidShorthands
open MonoidalUtilities.Shorthands M

private
  i⇒ = swapInner.from

op-⊠F : ∀ {a b} {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b} →
  Functor (Opposite.op S 𝒜 ⊠ Opposite.op S ℬ) (Opposite.op S (𝒜 ⊠ ℬ))
op-⊠F {𝒜 = 𝒜} {ℬ} = record
  { map₀ = λ X → X
  ; map₁ = id
  ; identity = identityˡ
  ; homomorphism = op-⊠-homomorphism
  }
  where
  module 𝒜 = Enriched.Category 𝒜
  module ℬ = Enriched.Category ℬ

  variable
    A B C : 𝒜.Obj
    X Y Z : ℬ.Obj

  abstract
    op-⊠-homomorphism : id ∘
        (((𝒜.⊚ {A = C} {B} {A} ∘ σ⇒) ⊗₁ (ℬ.⊚ {A = Z} {Y} {X} ∘ σ⇒)) ∘ i⇒)
      ≈ (((𝒜.⊚ ⊗₁ ℬ.⊚) ∘ i⇒) ∘ σ⇒) ∘ (id ⊗₁ id)
    op-⊠-homomorphism = begin
      id ∘ (((𝒜.⊚ ∘ σ⇒) ⊗₁ (ℬ.⊚ ∘ σ⇒)) ∘ i⇒)  ≈⟨ identityˡ ⟩
      ((𝒜.⊚ ∘ σ⇒) ⊗₁ (ℬ.⊚ ∘ σ⇒)) ∘ i⇒         ≈⟨ ⊗.homomorphism ⟩∘⟨refl ⟩
      ((𝒜.⊚ ⊗₁ ℬ.⊚) ∘ (σ⇒ ⊗₁ σ⇒)) ∘ i⇒        ≈⟨ extendˡ swapInner-braiding′ ⟩
      ((𝒜.⊚ ⊗₁ ℬ.⊚) ∘ i⇒) ∘ σ⇒                ≈⟨ introʳ ⊗.identity ⟩
      (((𝒜.⊚ ⊗₁ ℬ.⊚) ∘ i⇒) ∘ σ⇒) ∘ (id ⊗₁ id) ∎

swapF : ∀ {a b} {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b} →
  Functor (𝒜 ⊠ ℬ) (ℬ ⊠ 𝒜)
swapF {𝒜 = 𝒜} {ℬ} = record
  { map₀ = swap
  ; map₁ = σ⇒
  ; identity = swap-identity
  ; homomorphism = pullˡ σ⇒-comm ○ extendˡ swapInner-braidingʳ
  }
  where
  module 𝒜 = Enriched.Category 𝒜
  module ℬ = Enriched.Category ℬ

  abstract
    swap-identity : {A : 𝒜.Obj} {X : ℬ.Obj} →
                    σ⇒ {𝒜 [ A , A ]} {ℬ [ X , X ]} ∘ (𝒜.id ⊗₁ ℬ.id) ∘ λ⇐
                    ≈ (ℬ.id ⊗₁ 𝒜.id) ∘ λ⇐
    swap-identity = begin
      σ⇒ ∘ (𝒜.id ⊗₁ ℬ.id) ∘ λ⇐            ≈⟨ pullˡ σ⇒-comm ⟩
      ((ℬ.id ⊗₁ 𝒜.id) ∘ σ⇒) ∘ λ⇐          ≈⟨ pushʳ braiding-coherence-σ ⟩∘⟨refl ⟩
      (((ℬ.id ⊗₁ 𝒜.id) ∘ λ⇐) ∘ ρ⇒) ∘ λ⇐   ≈⟨ pullʳ (refl⟩∘⟨ coherence-inv₃) ⟩
      ((ℬ.id ⊗₁ 𝒜.id) ∘ λ⇐) ∘ ρ⇒ ∘ ρ⇐     ≈⟨ elimʳ unitorʳ.isoʳ ⟩
      (ℬ.id ⊗₁ 𝒜.id) ∘ λ⇐                 ∎

module LeftApplication {a b}
  (𝒜 : Enriched.Category M a) (ℬ : Enriched.Category M b) where

  private
    module 𝒜 = Enriched.Category 𝒜
    module ℬ = Enriched.Category ℬ
    module 𝒜⊠ℬ = Enriched.Category (𝒜 ⊠ ℬ)

    variable
      A : 𝒜.Obj
      X Y Z : ℬ.Obj
      W : Obj

    pairˡ : (A : 𝒜.Obj) → ℬ [ X , Y ] ⇒ (𝒜 ⊠ ℬ) [ (A , X) , (A , Y) ]
    pairˡ A = (𝒜.id ⊗₁ id) ∘ λ⇐

    abstract
      pairˡ-natural : (f : W ⇒ ℬ [ X , Y ]) → pairˡ A ∘ f ≈ (𝒜.id ⊗₁ f) ∘ λ⇐
      pairˡ-natural f = begin
        ((𝒜.id ⊗₁ id) ∘ λ⇐) ∘ f         ≈⟨ pullʳ unitorˡ-commute-to ⟩
        (𝒜.id ⊗₁ id) ∘ (id ⊗₁ f) ∘ λ⇐   ≈⟨ pullˡ merge₁ˡ ⟩
        ((𝒜.id ∘ id) ⊗₁ f) ∘ λ⇐         ≈⟨ identityʳ ⟩⊗⟨refl ⟩∘⟨refl ⟩
        (𝒜.id ⊗₁ f) ∘ λ⇐                ∎

      pairˡ-slide : i⇒ ∘ ((𝒜.id {A} ⊗₁ id {ℬ [ Y , Z ]}) ⊗₁ (𝒜.id {A} ⊗₁ id {ℬ [ X , Y ]}))
                    ≈ (((𝒜.id ⊗₁ 𝒜.id) ⊗₁ id) ∘ i⇒)
      pairˡ-slide = begin
        i⇒ ∘ ((𝒜.id ⊗₁ id) ⊗₁ (𝒜.id ⊗₁ id))   ≈⟨ interchange-natural ⟩
        ((𝒜.id ⊗₁ 𝒜.id) ⊗₁ (id ⊗₁ id)) ∘ i⇒   ≈⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟩
        ((𝒜.id ⊗₁ 𝒜.id) ⊗₁ id) ∘ i⇒           ∎

      pairˡ-actions : (𝒜.⊚ {A = A} ⊗₁ ℬ.⊚ {A = X} {Y} {Z}) ∘ ((𝒜.id ⊗₁ 𝒜.id) ⊗₁ id)
                      ≈ (𝒜.id ⊗₁ ℬ.⊚) ∘ (λ⇒ ⊗₁ id)
      pairˡ-actions = begin
        (𝒜.⊚ ⊗₁ ℬ.⊚) ∘ ((𝒜.id ⊗₁ 𝒜.id) ⊗₁ id)       ≈˘⟨ ⊗-distrib-over-∘ ⟩
        (𝒜.⊚ ∘ (𝒜.id ⊗₁ 𝒜.id)) ⊗₁ (ℬ.⊚ ∘ id)        ≈⟨ (refl⟩∘⟨ serialize₁₂) ⟩⊗⟨ identityʳ ⟩
        (𝒜.⊚ ∘ (𝒜.id ⊗₁ id) ∘ (id ⊗₁ 𝒜.id)) ⊗₁ ℬ.⊚  ≈⟨ pullˡ 𝒜.unitˡ ⟩⊗⟨refl ⟩
        (λ⇒ ∘ (id ⊗₁ 𝒜.id)) ⊗₁ ℬ.⊚                  ≈⟨ unitorˡ-commute-from ⟩⊗⟨refl ⟩
        (𝒜.id ∘ λ⇒) ⊗₁ ℬ.⊚                          ≈⟨ split₁ʳ ⟩
        (𝒜.id ⊗₁ ℬ.⊚) ∘ (λ⇒ ⊗₁ id)                  ∎

      pairˡ-⊚ : 𝒜⊠ℬ.⊚ {A = A , X} {A , Y} {A , Z} ∘ (pairˡ A ⊗₁ pairˡ A)
                ≈ (𝒜.id ⊗₁ ℬ.⊚) ∘ λ⇐
      pairˡ-⊚ {A = A} = let 𝒜⊗ℬ⊚ = 𝒜.⊚ ⊗₁ ℬ.⊚ in begin
        ((𝒜.⊚ ⊗₁ ℬ.⊚) ∘ i⇒) ∘ (pairˡ A ⊗₁ pairˡ A)                  ≈⟨ pushʳ ⊗.homomorphism ⟩
        ((𝒜⊗ℬ⊚ ∘ i⇒) ∘ ((𝒜.id ⊗₁ id) ⊗₁ (𝒜.id ⊗₁ id))) ∘ (λ⇐ ⊗₁ λ⇐) ≈⟨ extendˡ pairˡ-slide ⟩∘⟨refl ⟩
        ((𝒜⊗ℬ⊚ ∘ ((𝒜.id ⊗₁ 𝒜.id) ⊗₁ id)) ∘ i⇒) ∘ (λ⇐ ⊗₁ λ⇐)         ≈⟨ assoc²αε ⟩
        𝒜⊗ℬ⊚ ∘ ((𝒜.id ⊗₁ 𝒜.id) ⊗₁ id) ∘ i⇒ ∘ (λ⇐ ⊗₁ λ⇐)
          ≈⟨ glue◽◃ pairˡ-actions swapInner-unitˡ⁻¹ ⟩
        (𝒜.id ⊗₁ ℬ.⊚) ∘ λ⇐ ∎

      pairˡ-homomorphism : pairˡ A ∘ ℬ.⊚ {A = X} {Y} {Z}
                          ≈ 𝒜⊠ℬ.⊚ ∘ (pairˡ A ⊗₁ pairˡ A)
      pairˡ-homomorphism {A = A} = begin
        pairˡ A ∘ ℬ.⊚                 ≈⟨ pairˡ-natural ℬ.⊚ ⟩
        (𝒜.id ⊗₁ ℬ.⊚) ∘ λ⇐            ≈˘⟨ pairˡ-⊚ ⟩
        𝒜⊠ℬ.⊚ ∘ (pairˡ A ⊗₁ pairˡ A)  ∎

  includeˡ : 𝒜.Obj → Functor ℬ (𝒜 ⊠ ℬ)
  includeˡ A = record
    { map₀ = A ,_
    ; map₁ = pairˡ A
    ; identity = pairˡ-natural ℬ.id
    ; homomorphism = pairˡ-homomorphism
    }

open LeftApplication public

includeʳ : ∀ {a b} (𝒜 : Enriched.Category M a) (ℬ : Enriched.Category M b) →
  Enriched.Category.Obj ℬ → Functor 𝒜 (𝒜 ⊠ ℬ)
includeʳ 𝒜 ℬ B = swapF ∘F includeˡ ℬ 𝒜 B
