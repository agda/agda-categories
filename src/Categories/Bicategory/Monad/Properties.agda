{-# OPTIONS --without-K --safe #-}
module Categories.Bicategory.Monad.Properties where

open import Categories.Category
open import Categories.Bicategory.Instance.Cats
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Functor using (Functor)

import Categories.Bicategory.Monad as BicatMonad
import Categories.Monad as ElemMonad

import Categories.Morphism.Reasoning as MR

--------------------------------------------------------------------------------
-- Bicategorical Monads in Cat are the same as the more elementary
-- definition of Monads.
--
-- NOTE: 

CatMonad⇒Monad : ∀ {o ℓ e} → (T : BicatMonad.Monad (Cats o ℓ e)) → ElemMonad.Monad (BicatMonad.Monad.C T)
CatMonad⇒Monad T = record
  { F = T.T
  ; η = T.η
  ; μ = T.μ
  ; assoc = λ {X} → begin
    η T.μ X ∘ F₁ T.T (η T.μ X)               ≈⟨ intro-ids ⟩
    (η T.μ X ∘ (F₁ T.T (η T.μ X) ∘ id) ∘ id) ≈⟨ T.assoc ⟩
    (η T.μ X ∘ F₁ T.T id ∘ η T.μ (F₀ T.T X)) ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (identity T.T) ○ identityˡ) ⟩
    η T.μ X ∘ η T.μ (F₀ T.T X)               ∎
  ; sym-assoc = λ {X} → begin
    η T.μ X ∘ η T.μ (F₀ T.T X)                    ≈⟨ intro-F-ids ⟩
    η T.μ X ∘ (F₁ T.T id ∘ η T.μ (F₀ T.T X)) ∘ id ≈⟨ T.sym-assoc ⟩
    η T.μ X ∘ F₁ T.T (η T.μ X) ∘ id               ≈⟨ ∘-resp-≈ʳ identityʳ ⟩
    η T.μ X ∘ F₁ T.T (η T.μ X)                    ∎
  ; identityˡ = λ {X} → begin
    η T.μ X ∘ F₁ T.T (η T.η X)             ≈⟨ intro-ids ⟩
    η T.μ X ∘ (F₁ T.T (η T.η X) ∘ id) ∘ id ≈⟨ T.identityˡ ⟩
    id                                     ∎
  ; identityʳ = λ {X} → begin
    η T.μ X ∘ η T.η (F₀ T.T X)                    ≈⟨ intro-F-ids ⟩
    η T.μ X ∘ (F₁ T.T id ∘ η T.η (F₀ T.T X)) ∘ id ≈⟨ T.identityʳ ⟩
    id                                            ∎
  }
  where
    module T = BicatMonad.Monad T
    open Category (BicatMonad.Monad.C T)
    open HomReasoning
    open Equiv
    open MR (BicatMonad.Monad.C T)

    open NaturalTransformation
    open Functor

    intro-ids : ∀ {X Y Z} {f : Y ⇒ Z} {g : X ⇒ Y} → f ∘ g ≈ f ∘ (g ∘ id) ∘ id
    intro-ids = ⟺ (∘-resp-≈ʳ identityʳ) ○ ⟺ (∘-resp-≈ʳ identityʳ)

    intro-F-ids : ∀ {X Y Z} {f : F₀ T.T Y ⇒ Z} {g : X ⇒ F₀ T.T Y} → f ∘ g ≈ f ∘ (F₁ T.T id ∘ g) ∘ id
    intro-F-ids = ∘-resp-≈ʳ (⟺ identityˡ ○  ⟺ (∘-resp-≈ˡ (identity T.T))) ○ ⟺ (∘-resp-≈ʳ identityʳ)

Monad⇒CatMonad : ∀ {o ℓ e} {𝒞 : Category o ℓ e} → (T : ElemMonad.Monad 𝒞) → BicatMonad.Monad (Cats o ℓ e)
Monad⇒CatMonad {𝒞 = 𝒞} T = record
  { C = 𝒞
  ; T = T.F
  ; η = T.η
  ; μ = T.μ
  ; assoc = λ {X} → begin
    T.μ.η X ∘ (T.F.F₁ (T.μ.η X) ∘ id) ∘ id ≈⟨ eliminate-ids ⟩
    T.μ.η X ∘ T.F.F₁ (T.μ.η X)             ≈⟨ T.assoc ⟩
    T.μ.η X ∘ T.μ.η (T.F.F₀ X)             ≈⟨ ∘-resp-≈ʳ (⟺ identityˡ ○ ∘-resp-≈ˡ (⟺ T.F.identity)) ⟩
    T.μ.η X ∘ T.F.F₁ id ∘ T.μ.η (T.F.F₀ X) ∎
  ; sym-assoc = λ {X} → begin
    T.μ.η X ∘ (T.F.F₁ id ∘ T.μ.η (T.F.F₀ X)) ∘ id ≈⟨ eliminate-F-ids ⟩
    T.μ.η X ∘ T.μ.η (T.F.F₀ X)                    ≈⟨ T.sym-assoc ⟩
    T.μ.η X ∘ T.F.F₁ (T.μ.η X)                    ≈⟨ ∘-resp-≈ʳ (⟺ identityʳ) ⟩
    T.μ.η X ∘ T.F.F₁ (T.μ.η X) ∘ id               ∎
  ; identityˡ = λ {X} → begin
    T.μ.η X ∘ (T.F.F₁ (T.η.η X) ∘ id) ∘ id ≈⟨ eliminate-ids ⟩
    T.μ.η X ∘ T.F.F₁ (T.η.η X)             ≈⟨ T.identityˡ ⟩
    id                                     ∎
  ; identityʳ = λ {X} → begin
    (T.μ.η X ∘ (T.F.F₁ id ∘ T.η.η (T.F.F₀ X)) ∘ id) ≈⟨ eliminate-F-ids ⟩
    T.μ.η X ∘ T.η.η (T.F.F₀ X)                      ≈⟨ T.identityʳ ⟩
    id                                              ∎
  }
  where
    module T = ElemMonad.Monad T
    open Category 𝒞
    open HomReasoning
    open MR 𝒞

    eliminate-ids : ∀ {X Y Z} {f : Y ⇒ Z} {g : X ⇒ Y} →  f ∘ (g ∘ id) ∘ id ≈ f ∘ g
    eliminate-ids = ∘-resp-≈ʳ identityʳ ○ ∘-resp-≈ʳ identityʳ

    eliminate-F-ids : ∀ {X Y Z} {f : T.F.F₀ Y ⇒ Z} {g : X ⇒ T.F.F₀ Y} →  f ∘ (T.F.F₁ id ∘ g) ∘ id ≈ f ∘ g
    eliminate-F-ids = ∘-resp-≈ʳ identityʳ ○ ∘-resp-≈ʳ (∘-resp-≈ˡ T.F.identity ○ identityˡ)
