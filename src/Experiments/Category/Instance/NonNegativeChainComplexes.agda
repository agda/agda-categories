{-# OPTIONS --without-K --safe #-}


open import Categories.Category.Core
open import Experiments.Category.Abelian

module Experiments.Category.Instance.NonNegativeChainComplexes {o ℓ e} {𝒜 : Category o ℓ e} (abelian : Abelian 𝒜) where

open import Level

open import Data.Nat using (ℕ)

open import Categories.Morphism.Reasoning 𝒜

open Category 𝒜
open Abelian abelian

open HomReasoning
open Equiv

record ChainComplex : Set (o ⊔ ℓ ⊔ e) where
  field
    Chain        : ℕ → Obj
    boundary     : ∀ (n : ℕ) → Chain (ℕ.suc n) ⇒ Chain n
    bounary-zero : ∀ {n} → boundary n ∘ boundary (ℕ.suc n) ≈ zero⇒

record ChainMap (V W : ChainComplex) : Set (ℓ ⊔ e) where
  private
    module V = ChainComplex V
    module W = ChainComplex W
  field
    hom     : ∀ (n : ℕ) → V.Chain n ⇒ W.Chain n
    commute : ∀ {n : ℕ} → (hom n ∘ V.boundary n) ≈ (W.boundary n ∘ hom (ℕ.suc n))

ChainComplexes : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
ChainComplexes = record
  { Obj = ChainComplex
  ; _⇒_ = ChainMap
  ; _≈_ = λ f g →
    let module f = ChainMap f
        module g = ChainMap g
    in ∀ {n : ℕ} → f.hom n ≈ g.hom n
  ; id = record
    { hom = λ _ → id
    ; commute = id-comm-sym
    }
  ; _∘_ = λ {U} {V} {W} f g →
    let module U = ChainComplex U
        module V = ChainComplex V
        module W = ChainComplex W
        module f = ChainMap f
        module g = ChainMap g
    in record
      { hom = λ n → f.hom n ∘ g.hom n
      ; commute = λ {n} → begin
        (f.hom n ∘ g.hom n) ∘ U.boundary n               ≈⟨ pullʳ g.commute ⟩
        f.hom n ∘ V.boundary n ∘ g.hom (ℕ.suc n)         ≈⟨ extendʳ f.commute ⟩
        W.boundary n ∘ f.hom (ℕ.suc n) ∘ g.hom (ℕ.suc n) ∎
      }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record
    { refl = refl
    ; sym = λ eq → sym eq
    ; trans = λ eq₁ eq₂ → trans eq₁ eq₂
    }
  ; ∘-resp-≈ = λ eq₁ eq₂ → ∘-resp-≈ eq₁ eq₂
  }
