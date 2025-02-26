{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Object.Coproduct.Indexed {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Categories.Morphism.Reasoning.Core C

open Category C
open Equiv

record IndexedCoproductOf {i} {I : Set i} (P : I → Obj) : Set (i ⊔ o ⊔ e ⊔ ℓ) where
  field
    X : Obj

    ι : ∀ i → P i ⇒ X
    [_] : ∀ {Y} → (∀ i → P i ⇒ Y) → X ⇒ Y

    commute : ∀ {Y} (f : ∀ i → P i ⇒ Y) → ∀ i → [ f ] ∘ ι i ≈ f i
    unique : ∀ {Y} (h : X ⇒ Y) (f : ∀ i → P i ⇒ Y) → (∀ i → h ∘ ι i ≈ f i) → [ f ] ≈ h

  η : ∀ {Y} (h : X ⇒ Y) → [ (λ i → h ∘ ι i) ] ≈ h
  η h = unique _ _ λ _ → refl

  ∘[] : ∀ {Y Z} (f : ∀ i → P i ⇒ Y) (g : Y ⇒ Z) → g ∘ [ f ] ≈ [ (λ i → g ∘ f i) ]
  ∘[] f g = sym (unique _ _ λ i → pullʳ (commute _ _))

  []-cong : ∀ {Y} (f g : ∀ i → P i ⇒ Y) → (∀ i → f i ≈ g i) → [ f ] ≈ [ g ]
  []-cong f g eq = unique _ _ λ i → trans (commute _ _) (sym (eq i))

  unique′ : ∀ {Y} (h h′ : X ⇒ Y) → (∀ i → h′ ∘ ι i ≈ h ∘ ι i) → h′ ≈ h
  unique′ h h′ f = trans (sym (unique _ _ f)) (η _)

AllCoproductsOf : ∀ i → Set (o ⊔ ℓ ⊔ e ⊔ suc i)
AllCoproductsOf i = ∀ {I : Set i} (P : I → Obj) → IndexedCoproductOf P
