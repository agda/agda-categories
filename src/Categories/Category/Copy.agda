{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Data.Product using (_,_)

-- Copy categories as described by Cockett & Lack in "Restriction categories I"

module Categories.Category.Copy {o ℓ e} (𝒞 : Category o ℓ e) where
  open Category 𝒞

  record Copy : Set (suc (o ⊔ ℓ ⊔ e)) where
    field
      monoidal : Monoidal 𝒞
      symmetric : Symmetric monoidal

    open Symmetric symmetric

    private
      σ : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
      σ {X} {Y} = braiding.⇒.η (X , Y)

    field
      Δ : ∀ {A} → A ⇒ A ⊗₀ A
      natural : ∀ {A} {f : A ⇒ A} → Δ ∘ f ≈ (f ⊗₁ f) ∘ Δ
      cocomm : ∀ {A} → Δ ∘ σ {A} {A} ≈ Δ
      coassoc : ∀ {A} → associator.from ∘ (Δ ⊗₁ id) ∘ Δ {A} ≈ (id ⊗₁ Δ) ∘ Δ {A}

  record TotalCopy : Set (suc (o ⊔ ℓ ⊔ e)) where
    field
      monoidal : Monoidal 𝒞
      symmetric : Symmetric monoidal

    open Symmetric symmetric

    private
      σ : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
      σ {X} {Y} = braiding.⇒.η (X , Y)

    field
      Δ : ∀ {A} → A ⇒ A ⊗₀ A
      natural : ∀ {A B} {f : A ⇒ B} → Δ ∘ f ≈ (f ⊗₁ f) ∘ Δ {A}
      cocomm : ∀ {A} → Δ ∘ σ {A} {A} ≈ Δ
      coassoc : ∀ {A} → associator.from ∘ (Δ ⊗₁ id) ∘ Δ {A} ≈ (id ⊗₁ Δ) ∘ Δ {A}
      counit : ∀ {A} → A ⇒ unit
      counitorˡ : ∀ {A} → (counit ⊗₁ id) ∘ Δ {A} ≈ unitorˡ.to
      counitorʳ : ∀ {A} → (id ⊗₁ counit) ∘ Δ {A} ≈ unitorʳ.to