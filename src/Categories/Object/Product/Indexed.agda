{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- this module characterizes a category of all products indexed by I.
-- this notion formalizes a category with all products up to certain cardinal.
module Categories.Object.Product.Indexed {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Categories.Morphism.Reasoning C

open Category C
open Equiv
open HomReasoning

record IndexedProductOf {i} {I : Set i} (P : I → Obj) : Set (i ⊔ o ⊔ e ⊔ ℓ) where
  field
    -- the product
    X : Obj

    π   : ∀ i → X ⇒ P i
    ⟨_⟩ : ∀ {Y} → (∀ i → Y ⇒ P i) → Y ⇒ X

    commute : ∀ {Y} {f : ∀ i → Y ⇒ P i} {i} → π i ∘ ⟨ f ⟩ ≈ f i
    unique  : ∀ {Y} {h : Y ⇒ X} {f : ∀ i → Y ⇒ P i} → (∀ {i} → π i ∘ h ≈ f i) → ⟨ f ⟩ ≈ h

  η : ∀ {Y} (h : Y ⇒ X) → ⟨ (λ i → π i ∘ h) ⟩ ≈ h
  η h = unique refl

  ⟨⟩∘ : ∀ {Y Z} (f : ∀ i → Y ⇒ P i) (g : Z ⇒ Y) → ⟨ f ⟩ ∘ g ≈ ⟨ (λ i → f i ∘ g) ⟩
  ⟨⟩∘ f g = ⟺ (unique (pullˡ commute))

  ⟨⟩-cong : ∀ {Y} {f g : ∀ i → Y ⇒ P i} → (eq : ∀ {i} → f i ≈ g i) → ⟨ f ⟩ ≈ ⟨ g ⟩
  ⟨⟩-cong eq = unique (trans commute (⟺ eq))

  unique′ : ∀ {Y} {h h′ : Y ⇒ X} → (∀ {i} → π i ∘ h′ ≈ π i ∘ h) → h′ ≈ h
  unique′ f = trans (⟺ (unique f)) (η _)

AllProductsOf : ∀ i → Set (o ⊔ ℓ ⊔ e ⊔ suc i)
AllProductsOf i = ∀ {I : Set i} (P : I → Obj) → IndexedProductOf P
