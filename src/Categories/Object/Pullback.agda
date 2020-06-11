{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

module Categories.Object.Pullback {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Data.Product

open Category 𝒞

-- Pullback squares (https://ncatlab.org/nlab/show/pullback)

record Pullback {A B C} (f : A ⇒ C) (g : B ⇒ C) : Set (o ⊔ ℓ ⊔ e) where
  -- A pullback square is a limit of a diagram of shape:
  --
  --              B
  --              |
  --              |
  --              g
  --              |
  --              |
  -- A --- f ---> C
  --
  -- forming the commutative diagram:
  --
  --
  -- X --- pᴮ --- B
  -- |            |
  -- |            |
  -- pᴬ           g
  -- |            |
  -- |            |
  -- A --- f ---> C
  --
  -- which is unique up to unique isomorphism

  field
    X : Obj
    pᴬ : X ⇒ A
    pᴮ : X ⇒ B

    -- Pullback squares are commutative
    commutes : f ∘ pᴬ ≈ g ∘ pᴮ

    -- X is the terminal object with this property
    universal
      : ∀ {Y} (qᴬ : Y ⇒ A) (qᴮ : Y ⇒ B)
      → (f ∘ qᴬ ≈ g ∘ qᴮ)
      → Y ⇒ X

    -- X is unique up to isomorphism
    universal-unique
      : ∀ {Y}
          (qᴬ : Y ⇒ A)
          (qᴮ : Y ⇒ B)
          (commutes : f ∘ qᴬ ≈ g ∘ qᴮ)
      → (! : Y ⇒ X)
      → pᴬ ∘ ! ≈ qᴬ
      → pᴮ ∘ ! ≈ qᴮ
      → ! ≈ universal qᴬ qᴮ commutes

    -- the cone formed by the universality property is in fact a cone
    universal-commutes
      : ∀ {Y}
          (qᴬ : Y ⇒ A)
          (qᴮ : Y ⇒ B)
          (commutes : f ∘ qᴬ ≈ g ∘ qᴮ)
      → pᴬ ∘ universal qᴬ qᴮ commutes ≈ qᴬ
      × pᴮ ∘ universal qᴬ qᴮ commutes ≈ qᴮ
