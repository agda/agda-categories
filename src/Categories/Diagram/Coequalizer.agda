{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Categories.Diagram.Coequalizer {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning

open import Level

private
  variable
    A B C : Obj

record Coequalizer (f g : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj} : Obj
    arr   : B ⇒ obj

    equality   : arr ∘ f ≈ arr ∘ g
    coequalize : {h : B ⇒ C} → h ∘ f ≈ h ∘ g → obj ⇒ C
    universal  : {h : B ⇒ C} {eq : h ∘ f ≈ h ∘ g} → h ≈ coequalize eq ∘ arr
    unique     : {h : B ⇒ C} {i : obj ⇒ C} {eq : h ∘ f ≈ h ∘ g} → h ≈ i ∘ arr → i ≈ coequalize eq
