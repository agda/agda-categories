{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- this module characterizes a category of all products indexed by I.
-- this notion formalizes a category with all products up to certain cardinal.
module Categories.Category.Complete.IndexedProduct {o ℓ e} (C : Category o ℓ e) where

open import Level

open Category C

record IndexedProductOf {i} {I : Set i} (P : I → Obj) : Set (i ⊔ o ⊔ e ⊔ ℓ) where
  field
    -- the product
    X : Obj

    π   : ∀ i → X ⇒ P i
    ⟨_⟩ : ∀ {Y} → (∀ i → Y ⇒ P i) → Y ⇒ X

    commute : ∀ {Y} (f : ∀ i → Y ⇒ P i) → ∀ i → π i ∘ ⟨ f ⟩ ≈ f i
    unique  : ∀ {Y} (h : Y ⇒ X) (f : ∀ i → Y ⇒ P i) → (∀ i → π i ∘ h ≈ f i) → ⟨ f ⟩ ≈ h


record IndexedProduct {i} (I : Set i) : Set (i ⊔ o ⊔ e ⊔ ℓ) where
  field
    P         : I → Obj
    productOf : IndexedProductOf P

  open IndexedProductOf productOf public

AllProducts : ∀ i → Set (o ⊔ ℓ ⊔ e ⊔ suc i)
AllProducts i = (I : Set i) → IndexedProduct I
