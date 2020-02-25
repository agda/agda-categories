{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Pushout {o ℓ e} (C : Category o ℓ e) where

open Category C
open HomReasoning

open import Level

private
  variable
    A B X Y Z : Obj
    h h₁ h₂ j : A ⇒ B

record Pushout (f : X ⇒ Y) (g : X ⇒ Z) : Set (o ⊔ ℓ ⊔ e) where
  field
    {Q} : Obj
    i₁  : Y ⇒ Q
    i₂  : Z ⇒ Q

  field
    commute   : i₁ ∘ f ≈ i₂ ∘ g
    universal : h₁ ∘ f ≈ h₂ ∘ g → Q ⇒ cod h₁
    unique    : ∀ {eq : h₁ ∘ f ≈ h₂ ∘ g} →
                  j ∘ i₁ ≈ h₁ → j ∘ i₂ ≈ h₂ →
                  j ≈ universal eq

    universal∘i₁≈h₁  : ∀ {eq : h₁ ∘ f ≈ h₂ ∘ g} →
                         universal eq ∘ i₁ ≈ h₁
    universal∘i₂≈h₂  : ∀ {eq : h₁ ∘ f ≈ h₂ ∘ g} →
                         universal eq ∘ i₂ ≈ h₂
