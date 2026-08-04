{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Coherence for tensor products of enriched categories.

module Categories.Enriched.Category.TensorProduct.Properties
  {o ℓ e} {V : Category o ℓ e} {M : Monoidal V} (S : Symmetric M) where

open import Data.Product using (_,_)
open import Data.Product.Algebra using (×-assoc)
open import Function.Bundles using (Inverse)

import Categories.Category.Construction.Core V as Core
import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
import Categories.Category.Monoidal.Interchange.Braided as BraidedInterchange
import Categories.Category.Monoidal.Interchange.Symmetric as SymmetricInterchange
open import Categories.Category.Monoidal.Interchange using (HasInterchange)
open import Categories.Category.Monoidal.Properties M using (coherence-inv₁)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M using (_⊗ᵢ_; module Shorthands)
import Categories.Enriched.Category M as Enriched
import Categories.Enriched.Category.Properties as EnrichedProperties
open import Categories.Enriched.Category.Equivalence M using (StrongEquivalence; WeakInverse)
import Categories.Enriched.Category.TensorProduct
open import Categories.Enriched.Category.Underlying M using (Underlying)
open import Categories.Enriched.Functor M using (Functor; _∘F_)
  renaming (id to idF)
import Categories.Enriched.Functor.TensorProduct as TensorFunctor
import Categories.Enriched.Functor.TensorProduct.Symmetric as TensorSymmetric
open import Categories.Enriched.NaturalTransformation M
  using (module NaturalTransformation) renaming (id to idNT)
open import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M
  using (NaturalIsomorphism)
open import Categories.Morphism.Reasoning V

open Category V
open Monoidal M
open Core.Shorthands
open Shorthands

open Symmetric S using (braided; commutative)
open BraidedInterchange braided using () renaming (hasInterchange to interchange)
open BraidedProperties.Shorthands braided
open Categories.Enriched.Category.TensorProduct interchange using (_⊠_)
open TensorFunctor interchange using (_⊠F_)
open TensorSymmetric S using (swapF)

module Reassociation {v} (𝒜 ℬ 𝒞 : Enriched.Category v) where

  private
    open HasInterchange interchange using (module swapInner)
      renaming (swapInner to ι; assoc to interchange-assoc)
    open swapInner using () renaming (from to i⇒; to to i⇐)
    open SymmetricInterchange S using () renaming (swapInner-selfInverse to ι⁻¹≈ι)

    module 𝒜 = Enriched.Category 𝒜
    module ℬ = Enriched.Category ℬ
    module 𝒞 = Enriched.Category 𝒞
    module ×α = Inverse (×-assoc v 𝒜.Obj ℬ.Obj 𝒞.Obj)

    variable
      A₀ A₁ A₂ : 𝒜.Obj -- source, intermediate, and target in each factor
      B₀ B₁ B₂ : ℬ.Obj
      C₀ C₁ C₂ : 𝒞.Obj
      U₀ U₁ V₀ V₁ W₀ W₁ : Obj -- two composition layers in each tensor factor

    abstract
      unit-insertion : α⇒ {unit} {unit} {unit} ∘ (λ⇐ ⊗₁ id) ≈ λ⇐
      unit-insertion = begin
        α⇒ ∘ (λ⇐ ⊗₁ id)  ≈˘⟨ refl⟩∘⟨ coherence-inv₁ ⟩
        α⇒ ∘ α⇐ ∘ λ⇐     ≈⟨ cancelˡ associator.isoʳ ⟩
        λ⇐               ∎

    abstract
      α-id : α⇒ ∘ ((((𝒜.id {A₀} ⊗₁ ℬ.id {B₀}) ∘ λ⇐) ⊗₁ 𝒞.id {C₀}) ∘ λ⇐)
        ≈ (𝒜.id ⊗₁ ((ℬ.id ⊗₁ 𝒞.id) ∘ λ⇐)) ∘ λ⇐
      α-id = let
        identities : unit ⊗₀ (unit ⊗₀ unit) ⇒
          𝒜.hom A₀ A₀ ⊗₀ (ℬ.hom B₀ B₀ ⊗₀ 𝒞.hom C₀ C₀)
        identities = 𝒜.id ⊗₁ (ℬ.id ⊗₁ 𝒞.id)
        glue-unit = glue◽◃ assoc-commute-from unit-insertion
        in begin
        α⇒ ∘ ((((𝒜.id ⊗₁ ℬ.id) ∘ λ⇐) ⊗₁ 𝒞.id) ∘ λ⇐)         ≈⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
        α⇒ ∘ (((𝒜.id ⊗₁ ℬ.id) ⊗₁ 𝒞.id) ∘ (λ⇐ ⊗₁ id)) ∘ λ⇐   ≈⟨ extendʳ glue-unit ⟩
        identities ∘ λ⇐ ∘ λ⇐                                ≈⟨ refl⟩∘⟨ unitorˡ-commute-to ⟩
        identities ∘ (id ⊗₁ λ⇐) ∘ λ⇐                        ≈⟨ pullˡ merge₂ʳ ⟩
        (𝒜.id ⊗₁ ((ℬ.id ⊗₁ 𝒞.id) ∘ λ⇐)) ∘ λ⇐                ∎

    abstract
      interchange-assocᵢ :
        (associator {U₀} {V₀} {W₀} ⊗ᵢ associator {U₁} {V₁} {W₁})
          ∘ᵢ ι ∘ᵢ (ι ⊗ᵢ idᵢ)
        ≈ᵢ ι ∘ᵢ (idᵢ ⊗ᵢ ι) ∘ᵢ associator
      interchange-assocᵢ = ⌞ interchange-assoc ⌟

    abstract
      interchange-assoc⁻¹ :
        α⇐ {U₀ ⊗₀ U₁} {V₀ ⊗₀ V₁} {W₀ ⊗₀ W₁} ∘ ((id ⊗₁ i⇒) ∘ i⇒)
        ≈ ((i⇒ ⊗₁ id) ∘ i⇒) ∘ (α⇐ ⊗₁ α⇐)
      interchange-assoc⁻¹ = begin
        α⇐ ∘ ((id ⊗₁ i⇒) ∘ i⇒)          ≈⟨ sym-assoc ⟩
        (α⇐ ∘ (id ⊗₁ i⇒)) ∘ i⇒          ≈⟨ (refl⟩∘⟨ refl⟩⊗⟨ ι⁻¹≈ι) ⟩∘⟨ ι⁻¹≈ι ⟩
        (α⇐ ∘ (id ⊗₁ i⇐)) ∘ i⇐          ≈˘⟨ to-≈ interchange-assocᵢ ⟩
        ((i⇐ ⊗₁ id) ∘ i⇐) ∘ (α⇐ ⊗₁ α⇐)  ≈˘⟨ (ι⁻¹≈ι ⟩⊗⟨refl ⟩∘⟨ ι⁻¹≈ι) ⟩∘⟨refl ⟩
        ((i⇒ ⊗₁ id) ∘ i⇒) ∘ (α⇐ ⊗₁ α⇐)  ∎

    abstract
      α⇐-⊚ : α⇐ ∘
          ((𝒜.⊚ {A₀} {A₁} {A₂} ⊗₁
            ((ℬ.⊚ {B₀} {B₁} {B₂} ⊗₁ 𝒞.⊚ {C₀} {C₁} {C₂}) ∘ i⇒)) ∘ i⇒)
        ≈ ((((𝒜.⊚ ⊗₁ ℬ.⊚) ∘ i⇒) ⊗₁ 𝒞.⊚) ∘ i⇒) ∘ (α⇐ ⊗₁ α⇐)
      α⇐-⊚ = let
        ⊚³ : (((𝒜.hom A₁ A₂ ⊗₀ 𝒜.hom A₀ A₁) ⊗₀ (ℬ.hom B₁ B₂ ⊗₀ ℬ.hom B₀ B₁))
               ⊗₀ (𝒞.hom C₁ C₂ ⊗₀ 𝒞.hom C₀ C₁))
             ⇒ (𝒜.hom A₀ A₂ ⊗₀ ℬ.hom B₀ B₂) ⊗₀ 𝒞.hom C₀ C₂
        ⊚³ = (𝒜.⊚ ⊗₁ ℬ.⊚) ⊗₁ 𝒞.⊚
        glue-interchange = glue◽◃ assoc-commute-to interchange-assoc⁻¹
        in begin
        α⇐ ∘ ((𝒜.⊚ ⊗₁ ((ℬ.⊚ ⊗₁ 𝒞.⊚) ∘ i⇒)) ∘ i⇒)          ≈⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
        α⇐ ∘ ((𝒜.⊚ ⊗₁ (ℬ.⊚ ⊗₁ 𝒞.⊚)) ∘ ((id ⊗₁ i⇒) ∘ i⇒))  ≈⟨ glue-interchange ⟩
        ⊚³ ∘ (((i⇒ ⊗₁ id) ∘ i⇒) ∘ (α⇐ ⊗₁ α⇐))             ≈⟨ assoc²δα ⟩
        ((⊚³ ∘ (i⇒ ⊗₁ id)) ∘ i⇒) ∘ (α⇐ ⊗₁ α⇐)             ≈⟨ merge₁ʳ ⟩∘⟨refl ⟩∘⟨refl ⟩
        ((((𝒜.⊚ ⊗₁ ℬ.⊚) ∘ i⇒) ⊗₁ 𝒞.⊚) ∘ i⇒) ∘ (α⇐ ⊗₁ α⇐)  ∎

    abstract
      α-⊚ : α⇒ ∘
          (((𝒜.⊚ {A₀} {A₁} {A₂} ⊗₁ ℬ.⊚ {B₀} {B₁} {B₂}) ∘ i⇒)
            ⊗₁ 𝒞.⊚ {C₀} {C₁} {C₂}) ∘ i⇒
        ≈ ((𝒜.⊚ ⊗₁ ((ℬ.⊚ ⊗₁ 𝒞.⊚) ∘ i⇒)) ∘ i⇒) ∘ (α⇒ ⊗₁ α⇒)
      α-⊚ = ⟺ (conjugate-to (associator ⊗ᵢ associator) associator α⇐-⊚)

    abstract
      α⇐-id : α⇐ ∘
          ((𝒜.id {A₀} ⊗₁ ((ℬ.id {B₀} ⊗₁ 𝒞.id {C₀}) ∘ λ⇐)) ∘ λ⇐)
        ≈ (((𝒜.id ⊗₁ ℬ.id) ∘ λ⇐) ⊗₁ 𝒞.id) ∘ λ⇐
      α⇐-id = ⟺ (switch-fromtoˡ associator α-id)

  α⇒F : Functor ((𝒜 ⊠ ℬ) ⊠ 𝒞) (𝒜 ⊠ (ℬ ⊠ 𝒞))
  α⇒F = record
    { map₀ = ×α.to
    ; map₁ = α⇒
    ; identity = α-id
    ; homomorphism = α-⊚
    }

  α⇐F : Functor (𝒜 ⊠ (ℬ ⊠ 𝒞)) ((𝒜 ⊠ ℬ) ⊠ 𝒞)
  α⇐F = record
    { map₀ = ×α.from
    ; map₁ = α⇐
    ; identity = α⇐-id
    ; homomorphism = α⇐-⊚
    }

  private
    module L = Enriched.Category ((𝒜 ⊠ ℬ) ⊠ 𝒞)
    module R = Enriched.Category (𝒜 ⊠ (ℬ ⊠ 𝒞))
    module UL = Underlying ((𝒜 ⊠ ℬ) ⊠ 𝒞)
    module UR = Underlying (𝒜 ⊠ (ℬ ⊠ 𝒞))
    module Lₚ = EnrichedProperties M ((𝒜 ⊠ ℬ) ⊠ 𝒞)
    module Rₚ = EnrichedProperties M (𝒜 ⊠ (ℬ ⊠ 𝒞))

    α⇒∘α⇐ : NaturalIsomorphism (α⇒F ∘F α⇐F) idF
    α⇒∘α⇐ = record
      { from = record
        { comp = λ _ → R.id
        ; commute = Rₚ.id-commuteˡ associator.isoʳ
        }
      ; to = record
        { comp = λ _ → R.id
        ; commute = Rₚ.id-commuteʳ associator.isoʳ
        }
      ; iso = record { isoˡ = UR.identity² ; isoʳ = UR.identity² }
      }

    α⇐∘α⇒ : NaturalIsomorphism (α⇐F ∘F α⇒F) idF
    α⇐∘α⇒ = record
      { from = record
        { comp = λ _ → L.id
        ; commute = Lₚ.id-commuteˡ associator.isoˡ
        }
      ; to = record
        { comp = λ _ → L.id
        ; commute = Lₚ.id-commuteʳ associator.isoˡ
        }
      ; iso = record { isoˡ = UL.identity² ; isoʳ = UL.identity² }
      }

  ⊠-associator : StrongEquivalence ((𝒜 ⊠ ℬ) ⊠ 𝒞) (𝒜 ⊠ (ℬ ⊠ 𝒞))
  ⊠-associator = record
    { F = α⇒F
    ; G = α⇐F
    ; weak-inverse = record
      { F∘G≈id = α⇒∘α⇐
      ; G∘F≈id = α⇐∘α⇒
      }
    }

open Reassociation public

module ReassociationNaturality {v}
  {𝒜₀ 𝒜₁ ℬ₀ ℬ₁ 𝒞₀ 𝒞₁ : Enriched.Category v}
  (F : Functor 𝒜₀ 𝒜₁) (G : Functor ℬ₀ ℬ₁) (H : Functor 𝒞₀ 𝒞₁) where

  private
    module F = Functor F
    module G = Functor G
    module H = Functor H
    module 𝒜₀ = Enriched.Category 𝒜₀
    module ℬ₀ = Enriched.Category ℬ₀
    module 𝒞₀ = Enriched.Category 𝒞₀
    module 𝒟 = Enriched.Category (𝒜₁ ⊠ (ℬ₁ ⊠ 𝒞₁))
    module 𝒟ₚ = EnrichedProperties M (𝒜₁ ⊠ (ℬ₁ ⊠ 𝒞₁))
    module U𝒟 = Underlying (𝒜₁ ⊠ (ℬ₁ ⊠ 𝒞₁))

    variable
      A B : 𝒜₀.Obj -- source and target in each factor
      X Y : ℬ₀.Obj
      W Z : 𝒞₀.Obj

    α-natural : α⇒ ∘ ((F.₁ {A} {B} ⊗₁ G.₁ {X} {Y}) ⊗₁ H.₁ {W} {Z})
      ≈ (F.₁ ⊗₁ (G.₁ ⊗₁ H.₁)) ∘ α⇒
    α-natural = assoc-commute-from

  ⊠-associator-commute : NaturalIsomorphism
    (α⇒F 𝒜₁ ℬ₁ 𝒞₁ ∘F ((F ⊠F G) ⊠F H))
    ((F ⊠F (G ⊠F H)) ∘F α⇒F 𝒜₀ ℬ₀ 𝒞₀)
  ⊠-associator-commute = record
    { from = record
      { comp = λ _ → 𝒟.id
      ; commute = 𝒟ₚ.id-commuteˡ α-natural
      }
    ; to = record
      { comp = λ _ → 𝒟.id
      ; commute = 𝒟ₚ.id-commuteʳ α-natural
      }
    ; iso = record { isoˡ = U𝒟.identity² ; isoʳ = U𝒟.identity² }
    }

open ReassociationNaturality public

swap² : ∀ {v} (𝒜 ℬ : Enriched.Category v) →
  NaturalIsomorphism (swapF ∘F swapF) (idF {C = 𝒜 ⊠ ℬ})
swap² 𝒜 ℬ = record
  { from = record
    { comp = λ _ → 𝒜⊠ℬ.id
    ; commute = 𝒜⊠ℬₚ.id-commuteˡ commutative
    }
  ; to = record
    { comp = λ _ → 𝒜⊠ℬ.id
    ; commute = 𝒜⊠ℬₚ.id-commuteʳ commutative
    }
  ; iso = record { isoˡ = U𝒜⊠ℬ.identity² ; isoʳ = U𝒜⊠ℬ.identity² }
  }
  where
    module 𝒜⊠ℬ = Enriched.Category (𝒜 ⊠ ℬ)
    module U𝒜⊠ℬ = Underlying (𝒜 ⊠ ℬ)
    module 𝒜⊠ℬₚ = EnrichedProperties M (𝒜 ⊠ ℬ)

private
  swap-inverse : ∀ {v} (𝒜 ℬ : Enriched.Category v) →
    WeakInverse
      (swapF {𝒜 = 𝒜} {ℬ = ℬ})
      (swapF {𝒜 = ℬ} {ℬ = 𝒜})
  swap-inverse 𝒜 ℬ = record
    { F∘G≈id = swap² ℬ 𝒜
    ; G∘F≈id = swap² 𝒜 ℬ
    }

⊠-swap : ∀ {v} (𝒜 ℬ : Enriched.Category v) → StrongEquivalence (𝒜 ⊠ ℬ) (ℬ ⊠ 𝒜)
⊠-swap 𝒜 ℬ = record
  { F = swapF
  ; G = swapF
  ; weak-inverse = swap-inverse 𝒜 ℬ
  }

module SwapNaturality {v}
  {𝒜₀ 𝒜₁ ℬ₀ ℬ₁ : Enriched.Category v}
  (F : Functor 𝒜₀ 𝒜₁) (G : Functor ℬ₀ ℬ₁) where

  private
    module F = Functor F
    module G = Functor G
    module 𝒟 = Enriched.Category (ℬ₁ ⊠ 𝒜₁)
    module 𝒟ₚ = EnrichedProperties M (ℬ₁ ⊠ 𝒜₁)
    module U𝒟 = Underlying (ℬ₁ ⊠ 𝒜₁)

    module 𝒜₀ = Enriched.Category 𝒜₀
    module ℬ₀ = Enriched.Category ℬ₀

    variable
      A B : 𝒜₀.Obj -- source and target in each factor
      X Y : ℬ₀.Obj

  ⊠-swap-commute : NaturalIsomorphism (swapF ∘F (F ⊠F G)) ((G ⊠F F) ∘F swapF)
  ⊠-swap-commute = record
    { from = record
      { comp = λ _ → 𝒟.id
      ; commute = 𝒟ₚ.id-commuteˡ σ⇒-comm
      }
    ; to = record
      { comp = λ _ → 𝒟.id
      ; commute = 𝒟ₚ.id-commuteʳ σ⇒-comm
      }
    ; iso = record { isoˡ = U𝒟.identity² ; isoʳ = U𝒟.identity² }
    }

open SwapNaturality public
