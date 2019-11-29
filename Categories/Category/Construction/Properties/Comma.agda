{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Properties.Comma where

open import Level
open import Data.Product using (Σ; _,_; proj₁; proj₂; zip; map; swap)

open import Categories.Category
open import Categories.Category.Instance.One
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.NaturalTransformation using (module NaturalTransformation)
open import Categories.Category.Construction.Comma
open import Categories.Category.Product renaming (Product to _×_)
open import Categories.Category.Construction.Functors renaming (Functors to [_⇒_])
open import Categories.NaturalTransformation

import Categories.Category.Slice as S
import Categories.Morphism.Reasoning as Reas

private
  variable
    o ℓ e o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃ : Level

-- There's a projection functor down onto the A and B Categories
module _ {A : Category o₁ ℓ₁ e₁}  {B : Category o₂ ℓ₂ e₂} {C : Category o₃ ℓ₃ e₃} where
  open CommaObj
  open Comma⇒
  private
    module A = Category A
    module EA = A.Equiv
    module B = Category B
    module EB = B.Equiv
    module C = Category C

  module _ (S : Functor B C) (T : Functor A C) where

    S↓T⇒A×B : Functor (S ↓ T) (A × B)
    S↓T⇒A×B = record
      { F₀           = λ o → β o , α o
      ; F₁           = λ a → h a , g a
      ; identity     = EA.refl , EB.refl
      ; homomorphism = EA.refl , EB.refl
      ; F-resp-≈     = swap
      }

    induced-nat : NaturalTransformation (S ∘F Dom S T) (T ∘F Cod S T)
    induced-nat = record
      { η       = f
      ; commute = λ i → C.Equiv.sym (commute i)
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
            ((Category.op [ A ⇒ C ] × [ B ⇒ C ]) [ (s₁ , s₂) , (d₁ , d₂) ]) → Functor (s₁ ↓ s₂) (d₁ ↓ d₂)
  induced {s₁ = s₁} {d₁ = d₁} {s₂} {d₂} (m₁ , m₂) = record
    { F₀ = λ o → record
      { α = α o
      ; β = β o
      ; f =  m₂.η (β o) ∘ f o ∘ m₁.η (α o)
      }
    ; F₁ = λ {o₁} {o₂} a → record
      { g = g a
      ; h = h a
      ; commute = begin
        F₁ d₂ (h a) ∘ m₂.η (β o₁) ∘ f o₁ ∘ m₁.η (α o₁)   ≈˘⟨ pushˡ (m₂.commute (h a)) ⟩
        (m₂.η (β o₂) ∘ F₁ s₂ (h a)) ∘ f o₁ ∘ m₁.η (α o₁) ≈⟨ pullˡ (pullʳ (commute a)) ⟩
        (m₂.η (β o₂) ∘ f o₂ ∘ F₁ s₁ (g a)) ∘ m₁.η (α o₁) ≈˘⟨ extendˡ (extendˡ (m₁.commute (g a))) ⟩
        (m₂.η (β o₂) ∘ f o₂ ∘ m₁.η (α o₂)) ∘ F₁ d₁ (g a) ∎
      }
    ; identity = A.Equiv.refl , B.Equiv.refl
    ; homomorphism = A.Equiv.refl , B.Equiv.refl
    ; F-resp-≈ = λ f≈g → f≈g
    }
    where
    module A = Category A
    module B = Category B
    module m₁ = NaturalTransformation m₁
    module m₂ = NaturalTransformation m₂

module _ {C : Category o ℓ e} where
  open Category C
  open S C
  open SliceObj
  open Slice⇒
  open HomReasoning
  open CommaObj
  open Comma⇒
  open Reas C

  slice⇒comma : ∀ X → Functor (Slice X) (idF {C = C} ↓ const {C = One {o} {ℓ} {e}} X)
  slice⇒comma X = record
    { F₀           = λ X → record { f = arr X }
    ; F₁           = λ f → record { g = _ ; h = _ ; commute = identityˡ ○ ⟺ (△ f) }
    ; identity     = refl , _
    ; homomorphism = refl , _
    ; F-resp-≈     = λ eq → eq , _
    }

  comma⇒slice : ∀ X → Functor (idF {C = C} ↓ const {C = One {o} {ℓ} {e}} X) (Slice X)
  comma⇒slice X = record
    { F₀           = λ X → S.sliceobj (f X)
    ; F₁           = λ g → S.slicearr (⟺ (commute g) ○ identityˡ)
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = proj₁
    }

  comma-slice-equiv : ∀ X → StrongEquivalence (Slice X) (idF {C = C} ↓ const {C = One {o} {ℓ} {e}} X)
  comma-slice-equiv X = record
    { F            = slice⇒comma X
    ; G            = comma⇒slice X
    ; weak-inverse = record
      { F∘G≈id = record
        { F⇒G = record
          { η       = λ Y → record { commute = ⟺ id-comm }
          ; commute = λ g → ⟺ id-comm , _
          }
        ; F⇐G = record
          { η       = λ Y → record { commute = ⟺ id-comm }
          ; commute = λ g → ⟺ id-comm , _
          }
        ; iso = λ Y → record
          { isoˡ = identityˡ , _
          ; isoʳ = identityˡ , _
          }
        }
      ; G∘F≈id = record
        { F⇒G = record
          { η       = λ Y → S.slicearr identityʳ
          ; commute = λ g → ⟺ id-comm
          }
        ; F⇐G = record
          { η       = λ Y → S.slicearr identityʳ
          ; commute = λ g → ⟺ id-comm
          }
        ; iso = λ Y → record
          { isoˡ = identityˡ
          ; isoʳ = identityˡ
          }
        }
      }
    }
