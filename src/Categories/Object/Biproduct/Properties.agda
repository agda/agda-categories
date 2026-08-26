{-# OPTIONS --without-K --safe #-}

module Categories.Object.Biproduct.Properties where

open import Categories.Category
open import Categories.Object.Biproduct
open import Categories.Object.Coproduct
open import Categories.Object.Product

module _ {o ℓ e} (𝒞 : Category o ℓ e) where

  Biproduct⇒Product : ∀ {A B} → Biproduct 𝒞 A B → Product 𝒞 A B
  Biproduct⇒Product biproduct = record
    { A×B = A⊕B
    ; π₁ = π₁
    ; π₂ = π₂
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; project₁ = project₁
    ; project₂ = project₂
    ; unique = ⟨⟩-unique
    }
    where
      open Biproduct biproduct

  Biproduct⇒Coproduct : ∀ {A B} → Biproduct 𝒞 A B → Coproduct 𝒞 A B
  Biproduct⇒Coproduct biproduct = record
    { A+B = A⊕B
    ; i₁ = i₁
    ; i₂ = i₂
    ; [_,_] = [_,_]
    ; inject₁ = inject₁
    ; inject₂ = inject₂
    ; unique = []-unique
    }
    where
      open Biproduct biproduct
