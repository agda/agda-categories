{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Site {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Product using (Σ; _,_; ∃₂)

open Category C

private
  variable
    X Y Z : Obj

record Coverage {i} j {I : Obj → Set i}
                (covering₀ : ∀ {X} → I X → Obj)
                (covering₁ : ∀ {X} (i : I X) → covering₀ i ⇒ X) : Set (i ⊔ suc j ⊔ o ⊔ ℓ ⊔ e) where
  field
    J          : ∀ (g : Y ⇒ Z) → Set j
    universal₀ : ∀ {g : Y ⇒ Z} → J g → Obj
    universal₁ : ∀ {g : Y ⇒ Z} (j : J g) → universal₀ j ⇒ Y
    commute    : ∀ {g : Y ⇒ Z} (j : J g) → ∃₂ (λ i k → g ∘ universal₁ j ≈ covering₁ i ∘ k)

record Site i j : Set (suc i ⊔ suc j ⊔ o ⊔ ℓ ⊔ e) where
  field
    I         : Obj → Set i
    covering₀ : ∀ {X} → I X → Obj
    covering₁ : ∀ {X} (i : I X) → covering₀ i ⇒ X
    coverage  : Coverage j covering₀ covering₁

  module coverage = Coverage coverage
  open coverage public
