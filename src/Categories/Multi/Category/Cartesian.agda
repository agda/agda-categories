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
open import Data.List.Relation.Unary.All.Functional renaming (All to Env)
open import Data.Wrap using (get)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SetoidR


-- We use `Env` (i.e. `All`) to define a collection of multimorphisms from a common domain.
-- For example, if `Γ ⊢ A` is a type of terms, then `Env (Γ ⊢_) Δ` is a type
-- of simultaneous substitutions thereof.

-- The pattern is that we define what a Cartesian multicategory is together
-- with the category of contexts it yields.
-- For example, given the family of multimorphisms _⇒_, we can derive the
-- family _⇒ˢ_ of simultaneous morphisms (compare: simultaneous substitutions)
-- that form the morphisms in the category of contexts.

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
  _≈ˢ_ = [ _≈_ ]_∼_

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
  homˢ-setoid : ∀ {Γ Δ} → Setoid (o ⊔ ℓ) (o ⊔ e)
  homˢ-setoid {Γ} {Δ} = record { isEquivalence = equivˢ {Γ} {Δ} }

  module HomReasoning where
    private
      module Hom-setoid {Γ A} = SetoidR (hom-setoid {Γ} {A}) using
        (step-≈; step-≈˘; step-≡; step-≡˘; begin_; _∎)
      module Homˢ-setoid {Γ Δ} = SetoidR (homˢ-setoid {Γ} {Δ}) using () renaming
        ( step-≈ to step-≈ˢ; step-≈˘ to step-≈ˢ˘; step-≡ to step-≡ˢ
        ; step-≡˘ to step-≡ˢ˘; begin_ to beginˢ_; _∎ to _∎ˢ
        )
    open Hom-setoid public
    open Homˢ-setoid public using (beginˢ_; _∎ˢ)

    infixr 2 step-≈ˢ step-≈ˢ˘ step-≡ˢ step-≡ˢ˘

    step-≈ˢ = Homˢ-setoid.step-≈ˢ
    syntax step-≈ˢ x y≈z x≈y = x ≈ˢ⟨ x≈y ⟩ y≈z
    step-≈ˢ˘ = Homˢ-setoid.step-≈ˢ˘
    syntax step-≈ˢ˘ x y≈z y≈x = x ≈ˢ˘⟨ y≈x ⟩ y≈z
    step-≡ˢ = Homˢ-setoid.step-≡ˢ
    syntax step-≡ˢ x y≡z x≡y = x ≡ˢ⟨ x≡y ⟩ y≡z
    step-≡ˢ˘ = Homˢ-setoid.step-≡ˢ˘
    syntax step-≡ˢ˘ x y≡z y≡x = x ≡ˢ˘⟨ y≡x ⟩ y≡z

    infixr 4 _⟩∘⟨_ refl⟩∘⟨_ _⟩∘ˢ⟨_ reflˢ⟩∘ˢ⟨_
    infixl 5 _⟩∘⟨reflˢ _⟩∘ˢ⟨reflˢ
    _⟩∘⟨_ = ∘-resp-≈

    refl⟩∘⟨_ : ∀ {Γ Δ A} {f : Δ ⇒ A} {σ σ′ : Γ ⇒ˢ Δ} → σ ≈ˢ σ′ → f ∘ σ ≈ f ∘ σ′
    refl⟩∘⟨_ = refl ⟩∘⟨_

    _⟩∘⟨reflˢ : ∀ {Γ Δ A} {f f′ : Δ ⇒ A} {σ : Γ ⇒ˢ Δ} → f ≈ f′ → f ∘ σ ≈ f′ ∘ σ
    _⟩∘⟨reflˢ = _⟩∘⟨ reflˢ

    _⟩∘ˢ⟨_ = ∘ˢ-resp-≈

    reflˢ⟩∘ˢ⟨_ : ∀ {Γ Δ Θ} {σ : Δ ⇒ˢ Θ} {τ τ′ : Γ ⇒ˢ Δ} →
      τ ≈ˢ τ′ → σ ∘ˢ τ ≈ˢ σ ∘ˢ τ′
    reflˢ⟩∘ˢ⟨_ = reflˢ ⟩∘ˢ⟨_

    _⟩∘ˢ⟨reflˢ : ∀ {Γ Δ Θ} {σ σ′ : Δ ⇒ˢ Θ} {τ : Γ ⇒ˢ Δ} →
      σ ≈ˢ σ′ → σ ∘ˢ τ ≈ˢ σ′ ∘ˢ τ
    _⟩∘ˢ⟨reflˢ = _⟩∘ˢ⟨ reflˢ
