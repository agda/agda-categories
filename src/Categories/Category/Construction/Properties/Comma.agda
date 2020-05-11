{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Properties.Comma where

open import Level
open import Data.Product using (Σ; _,_; proj₁; proj₂; zip; map; swap; <_,_>; -,_)

open import Categories.Category
open import Categories.Category.Instance.One
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Construction.Constant using (const; constNat)
open import Categories.NaturalTransformation using (module NaturalTransformation)
open import Categories.Category.Construction.Comma
open import Categories.Category.Product renaming (Product to _×_)
open import Categories.Category.Construction.Functors renaming (Functors to [_⇒_])
open import Categories.NaturalTransformation renaming (id to idN)

import Categories.Category.Slice as Sl
import Categories.Morphism.Reasoning as Reas

private
  variable
    o ℓ e o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃ : Level
    C D E : Category o ℓ e

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
    private
      module S = Functor S
      module T = Functor T

    S↓T⇒A×B : Functor (S ↓ T) (A × B)
    S↓T⇒A×B = record
      { F₀           = < β , α >
      ; F₁           = < h , g >
      ; identity     = EA.refl , EB.refl
      ; homomorphism = EA.refl , EB.refl
      ; F-resp-≈     = swap
      }

    induced-nat : NaturalTransformation (S ∘F Dom S T) (T ∘F Cod S T)
    induced-nat = record
      { η           = f
      ; commute     = λ i → C.Equiv.sym (commute i)
      ; sym-commute = commute
      }

    module _ (S′ : Functor D B) (T′ : Functor E A) where
      private
        module S′ = Functor S′
        module T′ = Functor T′

      compose-F : Functor (S ∘F S′ ↓ T ∘F T′) (S ↓ T)
      compose-F = record
        { F₀           = λ X → record
          { f = f X
          }
        ; F₁           = λ i → record
          { g       = S′.F₁ (g i)
          ; h       = T′.F₁ (h i)
          ; commute = commute i
          }
        ; identity     = S′.identity , T′.identity
        ; homomorphism = S′.homomorphism , T′.homomorphism
        ; F-resp-≈     = map S′.F-resp-≈ T′.F-resp-≈
        }

    module _ (S′ : Functor D B) where
      private
        module S′ = Functor S′

      compose-Fˡ : Functor (S ∘F S′ ↓ T) (S ↓ T)
      compose-Fˡ = record
        { F₀           = λ X → record
          { f = f X
          }
        ; F₁           = λ i → record
          { g       = S′.F₁ (g i)
          ; h       = h i
          ; commute = commute i
          }
        ; identity     = S′.identity , A.Equiv.refl
        ; homomorphism = S′.homomorphism , A.Equiv.refl
        ; F-resp-≈     = map S′.F-resp-≈ λ eq → eq
        }

    module _ (T′ : Functor E A) where
      private
        module T′ = Functor T′

      compose-Fʳ : Functor (S ↓ T ∘F T′) (S ↓ T)
      compose-Fʳ = record
        { F₀           = λ X → record
          { f = f X
          }
        ; F₁           = λ i → record
          { g       = g i
          ; h       = T′.F₁ (h i)
          ; commute = commute i
          }
        ; identity     = B.Equiv.refl , T′.identity
        ; homomorphism = B.Equiv.refl , T′.homomorphism
        ; F-resp-≈     = map (λ eq → eq) T′.F-resp-≈
        }

  module _ {S S′ : Functor B C} {T T′ : Functor A C} (γ : NaturalTransformation S′ S) (δ : NaturalTransformation T T′) where
    private
      module S′ = Functor S′
      module T′ = Functor T′
      module γ  = NaturalTransformation γ
      module δ  = NaturalTransformation δ
      module S = Functor S
      module T = Functor T
      open C
      open HomReasoning
      open Equiv
      open Reas C

    -- functors between Comma categories along natural transformations
    along-nat : Functor (S ↓ T) (S′ ↓ T′)
    along-nat = record
      { F₀           = λ X → record
        { f = δ.η (β X) ∘ f X ∘ γ.η (α X)
        }
      ; F₁           = λ {X Y} i → record
        { g       = g i
        ; h       = h i
        ; commute = begin
          T′.F₁ (h i) ∘ δ.η (β X) ∘ f X ∘ γ.η (α X)   ≈⟨ sym-assoc ⟩
          (T′.F₁ (h i) ∘ δ.η (β X)) ∘ f X ∘ γ.η (α X) ≈˘⟨ center⁻¹ (δ.commute (h i)) refl ⟩
          δ.η (β Y) ∘ (T.F₁ (h i) ∘ f X) ∘ γ.η (α X)  ≈⟨ refl⟩∘⟨ pushˡ (commute i) ⟩
          δ.η (β Y) ∘ f Y ∘ S.F₁ (g i) ∘ γ.η (α X)    ≈˘⟨ pull-last (γ.commute (g i)) ⟩
          (δ.η (β Y) ∘ f Y ∘ γ.η (α Y)) ∘ S′.F₁ (g i) ∎
        }
      ; identity     = B.Equiv.refl , A.Equiv.refl
      ; homomorphism = B.Equiv.refl , A.Equiv.refl
      ; F-resp-≈     = λ eq → eq
      }

  along-natʳ : ∀ {T T′ : Functor A C} (S : Functor B C) (δ : NaturalTransformation T T′) → Functor (S ↓ T) (S ↓ T′)
  along-natʳ S = along-nat idN

  along-natˡ : ∀ {S S′ : Functor B C} (γ : NaturalTransformation S′ S) (T : Functor A C) → Functor (S ↓ T) (S′ ↓ T)
  along-natˡ γ T = along-nat γ idN

-- There's an induced functor from Functors category to Functors over Comma categories
module _ {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂} {C : Category o₃ ℓ₃ e₃} where
  open CommaObj
  open Comma⇒
  open Category C
  open Functor
  open HomReasoning
  open Reas C

  induced : {s₁ d₁ : Functor A C} {s₂ d₂ : Functor B C} →
            ((Category.op [ A ⇒ C ] × [ B ⇒ C ]) [ (s₁ , s₂) , (d₁ , d₂) ]) → Functor (s₁ ↓ s₂) (d₁ ↓ d₂)
  induced {s₁ = s₁} {d₁ = d₁} {s₂} {d₂} (m₁ , m₂) = record
    { F₀ = λ o → record
      { α = α o
      ; β = β o
      ; f = m₂.η (β o) ∘ f o ∘ m₁.η (α o)
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

module _ (F : Functor C D) where
  private
    module D = Category D

  along-natˡ′ : ∀ {A B} (f : A D.⇒ B) → Functor (B ↙ F) (A ↙ F)
  along-natˡ′ f = along-natˡ (constNat f) F

  along-natʳ′ : ∀ {A B} (f : A D.⇒ B) → Functor (F ↘ A) (F ↘ B)
  along-natʳ′ f = along-natʳ F (constNat f)

module _ {C : Category o ℓ e} where
  open Category C
  open Sl C
  open SliceObj
  open Slice⇒
  open HomReasoning
  open Equiv
  open CommaObj
  open Comma⇒
  open Reas C

  slice⇒comma : ∀ X → Functor (Slice X) (idF {C = C} ↓ const {C = One {o} {ℓ} {e}} X)
  slice⇒comma X = record
    { F₀           = λ X → record { f = arr X }
    ; F₁           = λ f → record { commute = identityˡ ○ ⟺ (△ f) }
    ; identity     = refl , _
    ; homomorphism = refl , _
    ; F-resp-≈     = λ eq → eq , _
    }

  comma⇒slice : ∀ X → Functor (idF {C = C} ↓ const {C = One {o} {ℓ} {e}} X) (Slice X)
  comma⇒slice X = record
    { F₀           = λ X → Sl.sliceobj (f X)
    ; F₁           = λ g → Sl.slicearr (⟺ (commute g) ○ identityˡ)
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
          { η           = λ _ → record { commute = id-comm-sym }
          ; commute     = λ _ → id-comm-sym , _
          ; sym-commute = λ _ → id-comm , _
          }
        ; F⇐G = record
          { η           = λ _ → record { commute = id-comm-sym }
          ; commute     = λ _ → id-comm-sym , _
          ; sym-commute = λ _ → id-comm , _
          }
        ; iso = λ Y → record
          { isoˡ = identityˡ , _
          ; isoʳ = identityˡ , _
          }
        }
      ; G∘F≈id = record
        { F⇒G = record
          { η           = λ _ → Sl.slicearr identityʳ
          ; commute     = λ _ → id-comm-sym
          ; sym-commute = λ _ → id-comm
          }
        ; F⇐G = record
          { η           = λ _ → Sl.slicearr identityʳ
          ; commute     = λ _ → id-comm-sym
          ; sym-commute = λ _ → id-comm
          }
        ; iso = λ _ → record
          { isoˡ = identityˡ
          ; isoʳ = identityˡ
          }
        }
      }
    }
