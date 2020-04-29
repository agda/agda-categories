{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Categories.Diagram.Pushout {o ℓ e} (C : Category o ℓ e) where

open Category C
open HomReasoning

open import Level

private
  variable
    A B E X Y Z : Obj

record Pushout (f : X ⇒ Y) (g : X ⇒ Z) : Set (o ⊔ ℓ ⊔ e) where
  field
    {Q} : Obj
    i₁  : Y ⇒ Q
    i₂  : Z ⇒ Q

  field
    commute   : i₁ ∘ f ≈ i₂ ∘ g
    universal : {h₁ : Y ⇒ B} {h₂ : Z ⇒ B} → h₁ ∘ f ≈ h₂ ∘ g → Q ⇒ B
    unique    : {h₁ : Y ⇒ E} {h₂ : Z ⇒ E} {j : Q ⇒ E} {eq : h₁ ∘ f ≈ h₂ ∘ g} →
                  j ∘ i₁ ≈ h₁ → j ∘ i₂ ≈ h₂ →
                  j ≈ universal eq

    universal∘i₁≈h₁  : {h₁ : Y ⇒ E} {h₂ : Z ⇒ E} {eq : h₁ ∘ f ≈ h₂ ∘ g} →
                         universal eq ∘ i₁ ≈ h₁
    universal∘i₂≈h₂  : {h₁ : Y ⇒ E} {h₂ : Z ⇒ E} {eq : h₁ ∘ f ≈ h₂ ∘ g} →
                         universal eq ∘ i₂ ≈ h₂
