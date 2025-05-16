{-# OPTIONS --without-K --safe #-}
open import Categories.Bicategory using (Bicategory)

module Categories.Bicategory.Object.Product {o ℓ e t} (𝒞 : Bicategory o ℓ e t) where

open import Level

open Bicategory 𝒞
open import Categories.Category using (_[_,_])
open import Categories.Morphism using (_≅_)
open import Categories.Morphism.HeterogeneousEquality
open import Categories.Morphism.Notation using (_[_≅_])

record Product  (A B : Obj) : Set (o ⊔ ℓ ⊔ e ⊔ t) where
  infix 10 ⟨_,_⟩₁ ⟨_,_⟩₂
  field
    A×B : Obj
    πa : A×B ⇒₁ A
    πb : A×B ⇒₁ B
    ⟨_,_⟩₁ : ∀ {Γ} → Γ ⇒₁ A → Γ ⇒₁ B → Γ ⇒₁ A×B
    ⟨_,_⟩₂ : ∀ {Γ}{fa ga : Γ ⇒₁ A}{fb gb : Γ ⇒₁ B}
           → fa ⇒₂ ga → fb ⇒₂ gb → ⟨ fa , fb ⟩₁ ⇒₂ ⟨ ga , gb ⟩₁

    β₁a : ∀ {Γ} f g → hom Γ A [ πa ∘₁ ⟨ f , g ⟩₁  ≅ f ]
    β₁b : ∀ {Γ} f g → hom Γ B [ πb ∘₁ ⟨ f , g ⟩₁  ≅ g ]
    β₂a : ∀ {Γ}{fa ga fb gb}(αa : hom Γ A [ fa , ga ])(αb : hom Γ B [ fb , gb ])
        → Along β₁a _ _ , β₁a _ _ [ πa ▷ ⟨ αa , αb ⟩₂ ≈ αa ]
    β₂b : ∀ {Γ}{fa ga fb gb}(αa : hom Γ A [ fa , ga ])(αb : hom Γ B [ fb , gb ])
        → Along β₁b _ _ , β₁b _ _ [ πb ▷ ⟨ αa , αb ⟩₂ ≈ αb ]

    η₁ : ∀ {Γ} p → hom Γ A×B [ p ≅ ⟨ πa ∘₁ p , πb ∘₁ p ⟩₁ ]
    η₂ : ∀ {Γ}{p p'}(ϕ : hom Γ A×B [ p , p' ])
       → Along (η₁ _) , (η₁ _) [ ϕ ≈ ⟨ πa ▷ ϕ , πb ▷ ϕ ⟩₂ ]
