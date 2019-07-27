{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor hiding (id)

-- Cocone over a Functor F (from shape category J into category C)
-- Also defines the category of cocones "over F"

module Categories.Diagram.Cocone
  {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where

open Category C

private
  module C = Category C
  module J = Category J
  variable
    X Y Z : Obj

open HomReasoning
open Functor F

open import Level
open import Data.Product
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
import Categories.Morphism as Mor
open Mor C
import Categories.Morphism.IsoEquiv as IsoEquiv
open IsoEquiv C

open import Categories.Morphism.Reasoning C

record Coapex (N : Obj) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
  field
    ψ       : (X : Category.Obj J) → F₀ X ⇒ N
    commute : ∀ {X Y} (f : J [ X , Y ]) → ψ Y ∘ F₁ f ≈ ψ X

record Cocone : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
  field
    {N}    : Obj
    coapex : Coapex N

  open Coapex coapex public

open Coapex
open Cocone

record Cocone⇒ (c c′ : Cocone) : Set (ℓ ⊔ e ⊔ o′) where
  field
    arr     : N c ⇒ N c′
    commute : ∀ {X} → arr ∘ ψ c X ≈ ψ c′ X

open Cocone⇒

Cocones : Category _ _ _
Cocones = record
  { Obj       = Cocone
  ; _⇒_       = Cocone⇒
  ; _≈_       = λ f g → arr f ≈ arr g
  ; id        = record { arr = id ; commute = identityˡ }
  ; _∘_       = λ {A B C} f g → record
    { arr     = arr f ∘ arr g
    ; commute = λ {X} → begin
      (arr f ∘ arr g) ∘ ψ A X ≈⟨ pullʳ (commute g) ⟩
      arr f ∘ ψ B X           ≈⟨ commute f ⟩
      ψ C X                   ∎
    }
  ; assoc     = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv     = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }

module Cocones = Category Cocones

private
  variable
    K K′ : Cocone
  module CM = Mor Cocones
  module CI = IsoEquiv Cocones

open CM using () renaming (_≅_ to _⇔_)
open CI using () renaming (_≃_ to _↮_)

cocone-resp-iso : ∀ (κ : Cocone) → Cocone.N κ ≅ X → Σ[ κ′ ∈ Cocone ] κ ⇔ κ′
cocone-resp-iso {X = X} κ κ≅X = record
  { coapex = record
    { ψ       = λ Y → from ∘ Cocone.ψ κ Y
    ; commute = λ f → pullʳ (Cocone.commute κ f)
    }
  } , record
  { from = record
    { arr     = from
    ; commute = refl
    }
  ; to   = record
    { arr     = to
    ; commute = cancelˡ isoˡ
    }
  ; iso  = record
    { isoˡ    = isoˡ
    ; isoʳ    = isoʳ
    }
  }
  where open _≅_ κ≅X
        open Cocone
        open Coapex

iso-cocone⇒iso-coapex : K ⇔ K′ → N K ≅ N K′
iso-cocone⇒iso-coapex K⇔K′ = record
  { from = arr from
  ; to   = arr to
  ; iso  = record
    { isoˡ = isoˡ
    ; isoʳ = isoʳ
    }
  }
  where open _⇔_ K⇔K′
