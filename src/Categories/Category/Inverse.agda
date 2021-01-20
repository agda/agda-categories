{-# OPTIONS --without-K --safe #-}
module Categories.Category.Inverse where

open import Level using (Level; suc; _⊔_)

open import Categories.Category
open import Data.Product
import Categories.Morphism

record Inverse {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C public
  open Definitions C public
  open Categories.Morphism C

  infix 10 _⁻¹

  field
    _⁻¹ : ∀ {A B} → (f : A ⇒ B)
        → ∃! _≈_ (λ f⁻¹ → (f ∘ f⁻¹ ∘ f ≈ f) × (f⁻¹ ∘ f ∘ f⁻¹ ≈ f⁻¹))
