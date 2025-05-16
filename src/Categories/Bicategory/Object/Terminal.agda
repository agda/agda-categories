{-# OPTIONS --without-K --safe #-}
open import Categories.Bicategory using (Bicategory)

module Categories.Bicategory.Object.Terminal {o ℓ e t} (𝒞 : Bicategory o ℓ e t) where

open Bicategory 𝒞
open import Level
open import Categories.Category using (_[_,_])
open import Categories.Morphism.HeterogeneousEquality using (Along_,_[_≈_])
open import Categories.Morphism.Notation using (_[_≅_])
open import Categories.Morphism using (_≅_)

record IsTerminal (⊤ : Obj) : Set (o ⊔ ℓ ⊔ e ⊔ t) where
  field
    !₁ : {A : Obj} → (A ⇒₁ ⊤)
    !₂ : {A : Obj} → !₁ {A} ⇒₂ !₁

    η₁ : ∀ {A} f → hom A ⊤ [ f ≅ !₁ ]
    η₂ : ∀ {A}{f g}(α : hom A ⊤ [ f , g ])
       → Along η₁ _ , η₁ _ [ α ≈ !₂ ]

