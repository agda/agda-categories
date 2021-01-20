{-# OPTIONS --without-K --safe #-}
module Categories.Category.Inverse where

open import Level using (Level; suc; _⊔_)

open import Categories.Category
open import Data.Product
import Categories.Morphism

record pseudo-iso {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  open Definitions C
  open Categories.Morphism C

  infix 10 _⁻¹
  field
    _⁻¹ : ∀ {A B} → (f : A ⇒ B) → B ⇒ A
    pseudo-iso₁ : ∀ {A B} {f : A ⇒ B} → f ∘ f ⁻¹ ∘ f ≈ f
    pseudo-iso₂ : ∀ {A B} {f : A ⇒ B} → f ⁻¹ ∘ f ∘ f ⁻¹ ≈ f ⁻¹


record Inverse {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  open Definitions C
  open Categories.Morphism C
  open pseudo-iso

  field
    piso : pseudo-iso C
    unique : ∀ {p : pseudo-iso C} {A B} → (f : A ⇒ B) → _⁻¹ piso f ≈ _⁻¹ p f
