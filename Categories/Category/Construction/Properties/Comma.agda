{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Properties.Comma where

open import Level
open import Data.Product using (Σ; _,_; proj₁; proj₂; zip; map)

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation using (module NaturalTransformation)
open import Categories.Category.Construction.Comma
open import Categories.Category.Product renaming (Product to _×_)
open import Categories.Category.Construction.Functors renaming (Functors to [_⇒_])
import Categories.Morphism.Reasoning as Reas

private
  variable
    o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃ : Level

-- There's a projection functor down onto the A and B Categories
module _ {A : Category o₁ ℓ₁ e₁}  {B : Category o₂ ℓ₂ e₂} {C : Category o₃ ℓ₃ e₃} where
  open CommaObj
  open Comma⇒
  private
    module A = Category A
    module EA = A.Equiv
    module B = Category B
    module EB = B.Equiv

  S↓T⇒B×A : (S : Functor B C) (T : Functor A C) → Functor (S ↓ T) (A × B)
  S↓T⇒B×A S T = record
    { F₀ = λ o → α o , β o
    ; F₁ = λ a → g a , h a
    ; identity = EA.refl , EB.refl
    ; homomorphism = EA.refl , EB.refl
    ; F-resp-≈ = λ f≈g → f≈g
    }

-- There's an induced functor from Functors category to Functors over Comma categories
module _ {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂} {C : Category o₃ ℓ₃ e₃} where
  open CommaObj
  open Comma⇒
  open Category C
  open Functor
  open HomReasoning
  open Reas C
  -- open Squares C

  induced : {s₁ d₁ : Functor A C} {s₂ d₂ : Functor B C} →
            ((Category.op [ A ⇒ C ] × [ B ⇒ C ]) [ (s₁ , s₂) , (d₁ , d₂) ]) → Functor (s₂ ↓ s₁) (d₂ ↓ d₁)
  induced {s₁ = s₁} {d₁ = d₁} {s₂} {d₂} (m₁ , m₂) = record
    { F₀ = λ o → record { α = α o ; β = β o ; f =  m₂.η (β o) ∘ f o ∘ m₁.η (α o) }
    ; F₁ = λ {o₁} {o₂} a → record { g = g a ; h = h a ; commutes = begin
        F₁ d₂ (h a) ∘ m₂.η (β o₁) ∘ f o₁ ∘ m₁.η (α o₁)     ≈˘⟨ pushˡ (m₂.commute (h a)) ⟩
        (m₂.η (β o₂) ∘ F₁ s₂ (h a)) ∘ f o₁ ∘ m₁.η (α o₁)   ≈⟨ pullˡ (pullʳ (commutes a)) ⟩
        (m₂.η (β o₂) ∘ f o₂ ∘ F₁ s₁ (g a)) ∘ m₁.η (α o₁)   ≈˘⟨ extendˡ (extendˡ (m₁.commute (g a))) ⟩
        (m₂.η (β o₂) ∘ f o₂ ∘ m₁.η (α o₂)) ∘ F₁ d₁ (g a)   ∎ }
    ; identity = A.Equiv.refl , B.Equiv.refl
    ; homomorphism = A.Equiv.refl , B.Equiv.refl
    ; F-resp-≈ = λ f≈g → f≈g
    }
    where
    module A = Category A
    module B = Category B
    module m₁ = NaturalTransformation m₁
    module m₂ = NaturalTransformation m₂
