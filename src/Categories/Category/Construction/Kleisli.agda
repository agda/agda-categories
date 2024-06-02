{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Kleisli where

open import Level

open import Categories.Category
open import Categories.Functor using (Functor; module Functor)
open import Categories.NaturalTransformation hiding (id)
open import Categories.Monad
import Categories.Morphism.Reasoning.Core as MR

private
  variable
    o ℓ e : Level

Kleisli : {𝒞 : Category o ℓ e} → Monad 𝒞 → Category o ℓ e
Kleisli {𝒞 = 𝒞} M = record
  { Obj       = Obj
  ; _⇒_       = λ A B → (A ⇒ F₀ B)
  ; _≈_       = _≈_
  ; _∘_       = λ f g → (μ.η _ ∘ F₁ f) ∘ g
  ; id        = η.η _
  ; assoc     = assoc′
  ; sym-assoc = Equiv.sym assoc′
  ; identityˡ = identityˡ′
  ; identityʳ = identityʳ′
  ; identity² = identity²′
  ; equiv     = equiv
  ; ∘-resp-≈  = λ f≈h g≈i → ∘-resp-≈ (∘-resp-≈ʳ (F-resp-≈ f≈h)) g≈i
  }
  where
  module M = Monad M
  open M using (μ; η; F)
  open Functor F
  open Category 𝒞
  open HomReasoning
  open MR 𝒞

  assoc′ : ∀ {A B C D} {f : A ⇒ F₀ B} {g : B ⇒ F₀ C} {h : C ⇒ F₀ D}
          → (μ.η D ∘ (F₁ ((μ.η D ∘ F₁ h) ∘ g))) ∘ f ≈ (μ.η D ∘ F₁ h) ∘ ((μ.η C ∘ F₁ g) ∘ f)
  assoc′ {A} {B} {C} {D} {f} {g} {h} = begin
    (μ.η D ∘ F₁ ((μ.η D ∘ F₁ h) ∘ g)) ∘ f           ≈⟨ pushʳ homomorphism ⟩∘⟨refl ⟩
    ((μ.η D ∘ F₁ (μ.η D ∘ F₁ h)) ∘ F₁ g) ∘ f        ≈⟨ pushˡ (∘-resp-≈ˡ (∘-resp-≈ʳ homomorphism)) ⟩
    (μ.η D ∘ (F₁ (μ.η D) ∘ F₁ (F₁ h))) ∘ (F₁ g ∘ f) ≈⟨ pushˡ (sym-glue M.assoc (μ.commute h)) ⟩
    (μ.η D ∘ F₁ h) ∘ (μ.η C ∘ (F₁ g ∘ f))           ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    (μ.η D ∘ F₁ h) ∘ ((μ.η C ∘ F₁ g) ∘ f)           ∎

  identityˡ′ : ∀ {A B} {f : A ⇒ F₀ B} → (μ.η B ∘ F₁ (η.η B)) ∘ f ≈ f
  identityˡ′ {A} {B} {f} = elimˡ M.identityˡ

  identityʳ′ : ∀ {A B} {f : A ⇒ F₀ B} → (μ.η B ∘ F₁ f) ∘ η.η A ≈ f
  identityʳ′ {A} {B} {f} = begin
        (μ.η B ∘ F₁ f) ∘ η.η A    ≈˘⟨ extendˡ (η.commute f) ⟩
        (μ.η B ∘ η.η (F₀ B)) ∘ f  ≈⟨ elimˡ M.identityʳ ⟩
        f                         ∎

  identity²′ : {A : Obj} → (μ.η A ∘ F₁ (η.η A)) ∘ η.η A ≈ η.η A
  identity²′ = elimˡ M.identityˡ
