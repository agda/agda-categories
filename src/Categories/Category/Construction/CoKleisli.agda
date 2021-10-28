{-# OPTIONS --without-K --safe #-}

-- Verbatim dual of Categories.Category.Construction.Kleisli
module Categories.Category.Construction.CoKleisli where

open import Level

open import Categories.Category
open import Categories.Functor using (Functor; module Functor)
open import Categories.NaturalTransformation hiding (id)
open import Categories.Comonad
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

CoKleisli : {𝒞 : Category o ℓ e} → Comonad 𝒞 → Category o ℓ e
CoKleisli {𝒞 = 𝒞} M =
 record
  { Obj       = Obj
  ; _⇒_       = λ A B → (F₀ A ⇒ B)
  ; _≈_       = _≈_
  ; _∘_       = λ f g → f ∘ F₁ g ∘ δ.η _
  ; id        = ε.η _
  ; assoc     = assoc′
  ; sym-assoc = Equiv.sym assoc′
  ; identityˡ = identityˡ′
  ; identityʳ = identityʳ′
  ; identity² = identity²′
  ; equiv     = equiv
  ; ∘-resp-≈  = λ f≈h g≈i → ∘-resp-≈ f≈h (∘-resp-≈ (F≈ g≈i) Equiv.refl)
  }
  where
  module M = Comonad M
  open M using (ε; δ; F)
  open Functor F
  open Category 𝒞
  open HomReasoning
  open MR 𝒞

  -- shorthands to make the proofs nicer
  F≈ = F-resp-≈

  assoc′ : {A B C D : Obj} {f : F₀ A ⇒ B} {g : F₀ B ⇒ C} {h : F₀ C ⇒ D} → (h ∘ F₁ g ∘ δ.η B) ∘ F₁ f ∘ δ.η A ≈ h ∘ F₁ (g ∘ F₁ f ∘ δ.η A) ∘ δ.η A
  assoc′ {A} {B} {C} {D} {f} {g} {h} =
      begin
        (h ∘ F₁ g ∘ δ.η B) ∘ (F₁ f ∘ δ.η A) ≈⟨ assoc ⟩
        h ∘ ((F₁ g ∘ δ.η B) ∘ (F₁ f ∘ δ.η A)) ≈⟨ ((refl⟩∘⟨ assoc)) ⟩
        h ∘ (F₁ g ∘ (δ.η B ∘ (F₁ f ∘ δ.η A))) ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ Equiv.sym assoc)) ⟩
        h ∘ (F₁ g ∘ ((δ.η B ∘ F₁ f) ∘ δ.η A)) ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ (δ.commute f ⟩∘⟨refl))) ⟩
        h ∘ (F₁ g ∘ ((F₁ (F₁ f) ∘ δ.η (F₀ A)) ∘ δ.η A)) ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ assoc)) ⟩
        h ∘ (F₁ g ∘ (F₁ (F₁ f) ∘ (δ.η (F₀ A) ∘ δ.η A))) ≈⟨ ((refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ Comonad.assoc M)))) ⟩
        h ∘ (F₁ g ∘ (F₁ (F₁ f) ∘ (F₁ (δ.η A) ∘ δ.η A))) ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ Equiv.sym assoc)) ⟩
        h ∘ (F₁ g ∘ ((F₁ (F₁ f) ∘ F₁ (δ.η A)) ∘ δ.η A)) ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ (Equiv.sym homomorphism ⟩∘⟨refl))) ⟩
        h ∘ (F₁ g ∘ (F₁ (F₁ f ∘ δ.η A) ∘ δ.η A)) ≈⟨ (refl⟩∘⟨ Equiv.sym assoc) ⟩
        h ∘ ((F₁ g ∘ F₁ (F₁ f ∘ δ.η A)) ∘ δ.η A) ≈⟨ (refl⟩∘⟨ (Equiv.sym homomorphism ⟩∘⟨refl)) ⟩
        h ∘ (F₁ (g ∘ (F₁ f ∘ δ.η A)) ∘ δ.η A)
      ∎

  identityˡ′ : ∀ {A B : Obj} {f : F₀ A ⇒ B} → ε.η B ∘ F₁ f ∘ δ.η A ≈ f
  identityˡ′ {A} {B} {f} =
    begin
      ε.η B ∘ F₁ f ∘ δ.η A ≈⟨ Equiv.sym assoc ⟩
      (ε.η B ∘ F₁ f) ∘ δ.η A ≈⟨ ∘-resp-≈ (ε.commute f) Equiv.refl ⟩
      (f ∘ ε.η (F₀ A)) ∘ δ.η A ≈⟨ assoc ⟩
      f ∘ ε.η (F₀ A) ∘ δ.η A ≈⟨ elimʳ (Comonad.identityʳ M) ⟩
      f
    ∎

  identityʳ′ : ∀ {A B : Obj} {f : F₀ A ⇒ B} → f ∘ F₁ (ε.η A) ∘ δ.η A ≈ f
  identityʳ′ {A} {B} {f} = elimʳ (Comonad.identityˡ M)

  identity²′ : {A : Obj} → ε.η A ∘ F₁ (ε.η A) ∘ δ.η A ≈ ε.η A
  identity²′ = elimʳ (Comonad.identityˡ M)