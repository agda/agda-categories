{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Coequalizer {o ℓ e} (C : Category o ℓ e) where

open Category C
open HomReasoning

open import Level

private
  variable
    A B : Obj
    h i : A ⇒ B

record Coequalizer (f g : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj} : Obj
    arr   : B ⇒ obj

    equality   : arr ∘ f ≈ arr ∘ g
    coequalize : h ∘ f ≈ h ∘ g → obj ⇒ cod h
    universal  : ∀ {eq : h ∘ f ≈ h ∘ g} → h ≈ coequalize eq ∘ arr
    unique     : ∀ {eq : h ∘ f ≈ h ∘ g} → h ≈ i ∘ arr → i ≈ coequalize eq
