-- The monad of actions of a monoid in a monoidal category
-- See https://ncatlab.org/nlab/show/action+monad

-- With the Cartesian monoidal structure on Sets or Setoids, this gives us the
-- Writer monad familiar from Haskell. With the Cocartesian monoidal structure,
-- noting that all objects in that monoidal category are monoids in a unique
-- way, this gives us the Either monad.

{-# OPTIONS --safe --without-K #-}

open import Categories.Category
open import Categories.Category.Monoidal

module Categories.Monad.Construction.Action {o ℓ e} {C : Category o ℓ e} (CM : Monoidal C) where

open import Categories.Category.Monoidal.Properties CM using (coherence-inv₁)
open import Categories.Category.Monoidal.Reasoning CM
open import Categories.Category.Monoidal.Utilities CM using (module Shorthands; pentagon-inv; triangle-inv)
open import Categories.Monad using (Monad)
open import Categories.Morphism.Reasoning C
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Properties using ([_]-resp-∘; [_]-resp-square; [_]-resp-inverse)
open import Categories.Object.Monoid CM using (Monoid)
open import Function.Base using (_$_)

open Category C
open Monoidal CM
open Shorthands

module _ (m : Monoid) where

  private
    module m = Monoid m

  ActionF : Endofunctor C
  ActionF = m.Carrier ⊗-

  private
    module A = Functor ActionF

    η : ∀ X → X ⇒ A.₀ X
    η X = m.η ⊗₁ id ∘ unitorˡ.to
 
    η-commute : ∀ {X Y} (f : X ⇒ Y) → η Y ∘ f ≈ A.₁ f ∘ η X
    η-commute f = glue (Equiv.sym [ ⊗ ]-commute) unitorˡ-commute-to

    μ : ∀ X → A.₀ (A.₀ X) ⇒ A.₀ X
    μ X = m.μ ⊗₁ id ∘ associator.to

    μ-commute : ∀ {X Y} (f : X ⇒ Y) → μ Y ∘ A.₁ (A.₁ f) ≈ A.₁ f ∘ μ X
    μ-commute f = glue (Equiv.sym [ ⊗ ]-commute) (assoc-commute-to ○ ∘-resp-≈ˡ (⊗-resp-≈ˡ ⊗.identity))

    μ-assoc : ∀ {X} → μ X ∘ A.₁ (μ X) ≈ μ X ∘ μ (A.₀ X)
    μ-assoc = begin
      (m.μ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ (m.μ ⊗₁ id ∘ α⇐)              ≈⟨ refl⟩∘⟨ Functor.homomorphism (_ ⊗-) ⟩
      (m.μ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ (m.μ ⊗₁ id) ∘ id ⊗₁ α⇐)      ≈⟨ extend² assoc-commute-to ⟩
      (m.μ ⊗₁ id ∘ (id ⊗₁ m.μ) ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ α⇐)      ≈⟨ [ -⊗ _ ]-resp-square (switch-fromtoʳ associator (assoc ○ Equiv.sym m.assoc)) ⟩∘⟨refl ⟩
      ((m.μ ∘ m.μ ⊗₁ id) ⊗₁ id ∘ α⇐ ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ α⇐) ≈⟨ pullʳ (sym-assoc ○ pentagon-inv) ⟩
      (m.μ ∘ m.μ ⊗₁ id) ⊗₁ id ∘ (α⇐ ∘ α⇐)                    ≈⟨ Functor.homomorphism (-⊗ _) ⟩∘⟨refl ⟩
      (m.μ ⊗₁ id ∘ (m.μ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ α⇐)            ≈⟨ extend² (Equiv.sym assoc-commute-to ○ ∘-resp-≈ʳ (⊗-resp-≈ʳ ⊗.identity)) ⟩
      (m.μ ⊗₁ id ∘ α⇐) ∘ (m.μ ⊗₁ id ∘ α⇐)                    ∎

    μ-identityˡ : ∀ {X} → μ X ∘ A.₁ (η X) ≈ id
    μ-identityˡ = begin
      (m.μ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ (m.η ⊗₁ id ∘ λ⇐)         ≈⟨ refl⟩∘⟨ Functor.homomorphism (_ ⊗-) ⟩
      (m.μ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ (m.η ⊗₁ id) ∘ id ⊗₁ λ⇐) ≈⟨ extend² assoc-commute-to ⟩
      (m.μ ⊗₁ id ∘ (id ⊗₁ m.η) ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ λ⇐) ≈⟨ [ -⊗ _ ]-resp-∘ (Equiv.sym m.identityʳ) ⟩∘⟨ triangle-inv ⟩
      ρ⇒ ⊗₁ id ∘ ρ⇐ ⊗₁ id                               ≈⟨ [ -⊗ _ ]-resp-inverse unitorʳ.isoʳ ⟩
      id                                                ∎

    μ-identityʳ : ∀ {X} → μ X ∘ η (A.₀ X) ≈ id
    μ-identityʳ = begin
      (m.μ ⊗₁ id ∘ α⇐) ∘ (m.η ⊗₁ id ∘ λ⇐)         ≈⟨ extend² (∘-resp-≈ʳ (⊗-resp-≈ʳ (Equiv.sym ⊗.identity)) ○ assoc-commute-to) ⟩
      (m.μ ⊗₁ id ∘ (m.η ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ λ⇐) ≈⟨ [ -⊗ _ ]-resp-∘ (Equiv.sym m.identityˡ) ⟩∘⟨ coherence-inv₁ ⟩
      λ⇒ ⊗₁ id ∘ λ⇐ ⊗₁ id                         ≈⟨ [ -⊗ _ ]-resp-inverse unitorˡ.isoʳ ⟩
      id                                          ∎

  ActionM : Monad C
  ActionM = record
    { F = ActionF
    ; η = ntHelper record
      { η = η
      ; commute = η-commute
      }
    ; μ = ntHelper record
      { η = μ
      ; commute = μ-commute
      }
    ; assoc = μ-assoc
    ; sym-assoc = Equiv.sym μ-assoc
    ; identityˡ = μ-identityˡ
    ; identityʳ = μ-identityʳ
    }
