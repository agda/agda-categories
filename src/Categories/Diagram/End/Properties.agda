{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.End.Properties where

open import Level
open import Data.Product using (Σ; _,_)
open import Function using (_$_)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Construction.Functors
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Dinatural
open import Categories.Diagram.End as ∫

import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

module _ {C : Category o ℓ e}
         (F : Functor E (Functors (Product (Category.op C) C) D)) where
  private
    module C = Category C
    module D = Category D
    module E = Category E
    module NT = NaturalTransformation
  open D
  open HomReasoning

  open MR D
  open Functor F
  open End hiding (E)
  open NT using (η)

  EndF : (∀ X → End (F₀ X)) → Functor E D
  EndF end = record
    { F₀           = λ X → End.E (end X)
    ; F₁           = F₁′
    ; identity     = λ {A} → unique (end A) (id-comm ○ ∘-resp-≈ˡ (⟺ identity))
    ; homomorphism = λ {A B C} {f g} → unique (end C) $ λ {Z} → begin
      dinatural.α (end C) Z ∘ F₁′ g ∘ F₁′ f                       ≈⟨ pullˡ (universal (end C)) ⟩
      (η (F₁ g) (Z , Z) ∘ dinatural.α (end B) Z) ∘ F₁′ f          ≈⟨ pullʳ (universal (end B)) ⟩
      η (F₁ g) (Z , Z) ∘ η (F₁ f) (Z , Z) ∘ dinatural.α (end A) Z ≈˘⟨ pushˡ homomorphism ⟩
      η (F₁ (g E.∘ f)) (Z , Z) ∘ dinatural.α (end A) Z            ∎
    ; F-resp-≈     = λ {A B f g} eq → unique (end B) $ λ {Z} → begin
      dinatural.α (end B) Z ∘ F₁′ g                               ≈⟨ universal (end B) ⟩
      η (F₁ g) (Z , Z) ∘ dinatural.α (end A) Z                    ≈˘⟨ F-resp-≈ eq ⟩∘⟨refl ⟩
      η (F₁ f) (Z , Z) ∘ dinatural.α (end A) Z                    ∎
    }
    where F₁′ : ∀ {X Y} → X E.⇒ Y → End.E (end X) ⇒ End.E (end Y)
          F₁′ {X} {Y} f = factor (end Y) $ record
            { E         = End.E (end X)
            ; dinatural = F₁ f <∘ dinatural (end X)
            }
