{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Categories.Diagram.Pushout {o ℓ e} (C : Category o ℓ e) where

open Category C
open HomReasoning
open Equiv

open import Categories.Morphism.Reasoning C as Square
  renaming (glue to glue-square) hiding (id-unique)

open import Level

private
  variable
    A B E X Y Z : Obj
    f g h j : A ⇒ B

record Pushout (f : X ⇒ Y) (g : X ⇒ Z) : Set (o ⊔ ℓ ⊔ e) where
  field
    {Q} : Obj
    i₁  : Y ⇒ Q
    i₂  : Z ⇒ Q

  field
    commute         : i₁ ∘ f ≈ i₂ ∘ g
    universal       : {h₁ : Y ⇒ B} {h₂ : Z ⇒ B} → h₁ ∘ f ≈ h₂ ∘ g → Q ⇒ B
    universal∘i₁≈h₁ : {h₁ : Y ⇒ E} {h₂ : Z ⇒ E} {eq : h₁ ∘ f ≈ h₂ ∘ g} →
                        universal eq ∘ i₁ ≈ h₁
    universal∘i₂≈h₂ : {h₁ : Y ⇒ E} {h₂ : Z ⇒ E} {eq : h₁ ∘ f ≈ h₂ ∘ g} →
                        universal eq ∘ i₂ ≈ h₂
    unique-diagram  : h ∘ i₁ ≈ j ∘ i₁ → h ∘ i₂ ≈ j ∘ i₂ → h ≈ j

  unique : {h₁ : Y ⇒ E} {h₂ : Z ⇒ E} {eq : h₁ ∘ f ≈ h₂ ∘ g} →
             j ∘ i₁ ≈ h₁ → j ∘ i₂ ≈ h₂ → j ≈ universal eq
  unique j∘i₁≈h₁ j∘i₂≈h₂ =
    unique-diagram
      (j∘i₁≈h₁ ○ ⟺ universal∘i₁≈h₁)
      (j∘i₂≈h₂ ○ ⟺ universal∘i₂≈h₂)
