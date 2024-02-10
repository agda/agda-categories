{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory.Adjunction where

open import Categories.Bicategory
import Categories.Bicategory.Extras as Extras
open import Categories.Category
open import Level

private
  variable
    o ℓ e t : Level

module _ (𝒞 : Bicategory o ℓ e t) where
  open Bicategory 𝒞

  record Adjunction (A B : Obj) : Set (o ⊔ ℓ ⊔ e ⊔ t) where
    private
      module C = Extras 𝒞

    field
      L : A ⇒₁ B
      R : B ⇒₁ A

    field
      unit : id₁ ⇒₂ R ⊚₀ L
      counit : L ⊚₀ R ⇒₂ id₁

    private
{-
      L 1 → L (R L) → (L R) L
                          ↓           L 1
                        1 ∘ L      ~   ↓
                          ↓            L
                          L
-}
      l-triangle-l : L ⊚₀ id₁ ⇒₂ L
      l-triangle-l = C.unitorˡ.from ∘ᵥ (counit ⊚₁ id₂) ∘ᵥ C.associator.to ∘ᵥ (id₂ ⊚₁ unit)

      l-triangle-r : L ⊚₀ id₁ ⇒₂ L
      l-triangle-r = C.unitorʳ.from
{-
      1 R → (R L) R → R (L R)
                          ↓           L 1
                        R ∘ id     ~   ↓
                          ↓            L
                          R
-}
      r-triangle-l : id₁ ⊚₀ R ⇒₂ R
      r-triangle-l = C.unitorʳ.from ∘ᵥ (id₂ ⊚₁ counit) ∘ᵥ C.associator.from ∘ᵥ (unit ⊚₁ id₂)

      r-triangle-r : id₁ ⊚₀ R ⇒₂ R
      r-triangle-r = C.unitorˡ.from
    field
      l-triangle : l-triangle-l C.≈ l-triangle-r
      r-triangle : r-triangle-l C.≈ r-triangle-r
