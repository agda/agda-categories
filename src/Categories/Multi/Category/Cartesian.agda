{-# OPTIONS --without-K --safe #-}

-- Idea:
-- Whereas ordinary multicategories are based around the notion of substitution
-- from noncommutative linear (Lambek) logic, Cartesian multicategories are
-- based around the notion of substitution from intuitionistic logic, which is
-- a lot simpler. A representable Cartesian multicategory is exactly a
-- Cartesian category.
--
-- See https://ncatlab.org/nlab/show/cartesian+multicategory, particularly the
-- section “Alternative presentation”
-- (https://ncatlab.org/nlab/show/cartesian+multicategory#alternative_presentation).

module Categories.Multi.Category.Cartesian where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Wrap
open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SetoidR

infix 4 [_]_≈ᵉ_

Env : ∀ {o ℓ} {X : Set o} (V : X → Set ℓ) (Δ : List X) → Set (o ⊔ ℓ)
Env V Δ = ∀ {y} → y ∈ Δ → V y

[_]_≈ᵉ_ : ∀ {o ℓ e} {X : Set o} {V : X → Set ℓ} {Δ} →
  (∀ {x} → Rel (V x) e) → Rel (Env V Δ) (o ⊔ e)
[_]_≈ᵉ_ = Wrap λ _≈_ ρ σ → ∀ {y} (i : y ∈ _) → ρ i ≈ σ i

record CartesianMultiCategory (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix 4 _≈_ _≈ˢ_ _⇒_ _⇒ˢ_
  infixl 9 _∘_ _∘ˢ_

  field
    Obj : Set o
    _⇒_ : List Obj → Obj → Set ℓ
    _≈_ : ∀ {Γ A} (f g : Γ ⇒ A) → Set e

  _⇒ˢ_ : List Obj → List Obj → Set (o ⊔ ℓ)
  Γ ⇒ˢ Δ = Env (Γ ⇒_) Δ

  _≈ˢ_ : ∀ {Γ Δ} (σ τ : Γ ⇒ˢ Δ) → Set (o ⊔ e)
  _≈ˢ_ = [ _≈_ ]_≈ᵉ_

  field
    id : ∀ {Γ A} → A ∈ Γ → Γ ⇒ A
    _∘_ : ∀ {Γ Δ A} → Δ ⇒ A → Γ ⇒ˢ Δ → Γ ⇒ A

  idˢ : ∀ {Γ} → Γ ⇒ˢ Γ
  idˢ = id

  _∘ˢ_ : ∀ {Γ Δ Θ} → Δ ⇒ˢ Θ → Γ ⇒ˢ Δ → Γ ⇒ˢ Θ
  (σ ∘ˢ τ) i = σ i ∘ τ

  field
    equiv : ∀ {Γ A} → IsEquivalence (_≈_ {Γ} {A})

    ∘-resp-≈ : ∀ {Γ Δ A} {f f′ : Δ ⇒ A} {σ σ′ : Γ ⇒ˢ Δ} →
      f ≈ f′ → σ ≈ˢ σ′ → f ∘ σ ≈ f′ ∘ σ′

    identityˡ : ∀ {Γ Δ A} {i : A ∈ Δ} {σ : Γ ⇒ˢ Δ} → id i ∘ σ ≈ σ i
    identityʳ : ∀ {Γ A} {f : Γ ⇒ A} → f ∘ idˢ ≈ f
    assoc : ∀ {Γ Δ Θ A} {f : Θ ⇒ A} {σ : Δ ⇒ˢ Θ} {τ : Γ ⇒ˢ Δ} →
      f ∘ σ ∘ τ ≈ f ∘ (σ ∘ˢ τ)

  module Equiv {Γ A} = IsEquivalence (equiv {Γ} {A})

  private
    open Equiv
    reflˢ : ∀ {Γ Δ} {σ : Γ ⇒ˢ Δ} → σ ≈ˢ σ
    reflˢ .get i = refl
    transˢ : ∀ {Γ Δ} {σ τ υ : Γ ⇒ˢ Δ} → σ ≈ˢ τ → τ ≈ˢ υ → σ ≈ˢ υ
    transˢ p q .get i = trans (p .get i) (q .get i)
    symˢ : ∀ {Γ Δ} {σ τ : Γ ⇒ˢ Δ} → σ ≈ˢ τ → τ ≈ˢ σ
    symˢ p .get i = sym (p .get i)

  equivˢ : ∀ {Γ Δ} → IsEquivalence (_≈ˢ_ {Γ} {Δ})
  equivˢ = record { refl = reflˢ ; sym = symˢ ; trans = transˢ }
  module Equivˢ {Γ Δ} = IsEquivalence (equivˢ {Γ} {Δ}) renaming
    ( refl to reflˢ; trans to transˢ; sym to symˢ; reflexive to reflexiveˢ
    ; isPartialEquivalence to isPartialEquivalenceˢ
    )

  ∘ˢ-resp-≈ : ∀ {Γ Δ Θ} {σ σ′ : Δ ⇒ˢ Θ} {τ τ′ : Γ ⇒ˢ Δ} →
    σ ≈ˢ σ′ → τ ≈ˢ τ′ → σ ∘ˢ τ ≈ˢ σ′ ∘ˢ τ′
  ∘ˢ-resp-≈ p q .get i = ∘-resp-≈ (p .get i) q

  identityˡˢ : ∀ {Γ Δ} {σ : Γ ⇒ˢ Δ} → idˢ ∘ˢ σ ≈ˢ σ
  identityˡˢ .get i = identityˡ
  identityʳˢ : ∀ {Γ Δ} {σ : Γ ⇒ˢ Δ} → σ ∘ˢ idˢ ≈ˢ σ
  identityʳˢ .get i = identityʳ
  assocˢ : ∀ {Γ Δ Θ Λ} {σ : Θ ⇒ˢ Λ} {τ : Δ ⇒ˢ Θ} {υ : Γ ⇒ˢ Δ} →
    (σ ∘ˢ τ) ∘ˢ υ ≈ˢ σ ∘ˢ (τ ∘ˢ υ)
  assocˢ .get i = assoc

  hom-setoid : ∀ {Γ A} → Setoid ℓ e
  hom-setoid {Γ} {A} = record { isEquivalence = equiv {Γ} {A} }
  homˢ-setoid : ∀ {Γ Δ} → Setoid ℓ e
  homˢ-setoid {Γ} {Δ} = record { isEquivalence = equiv {Γ} {Δ} }

  module HomReasoning {Γ A} where
    open SetoidR (hom-setoid {Γ} {A}) public

  module HomˢReasoning {Γ Δ} where
    open SetoidR (homˢ-setoid {Γ} {Δ}) public
