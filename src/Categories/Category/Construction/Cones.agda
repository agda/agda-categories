{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor hiding (id)

-- category of cones "over a Functor F"

module Categories.Category.Construction.Cones
  {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where

open import Data.Product
import Categories.Diagram.Cone as Co
import Categories.Morphism as Mor
import Categories.Morphism.IsoEquiv as IsoEquiv
import Categories.Morphism.Reasoning as Reas

open Category C
open HomReasoning
open Mor C using (_≅_)
open IsoEquiv C using (_≃_; ⌞_⌟)
open Reas C

open Co F public
open Apex
open Cone
open Cone⇒

Cones : Category _ _ _
Cones = record
  { Obj       = Cone
  ; _⇒_       = Cone⇒
  ; _≈_       = λ f g → arr f ≈ arr g
  ; id        = record
    { arr     = id
    ; commute = identityʳ
    }
  ; _∘_       = λ {A B C} f g → record
    { arr     = arr f ∘ arr g
    ; commute = λ {X} → begin
      ψ C X ∘ arr f ∘ arr g ≈⟨ pullˡ (commute f) ⟩
      ψ B X ∘ arr g         ≈⟨ commute g ⟩
      ψ A X                 ∎
    }
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record
    { refl  = Equiv.refl
    ; sym   = Equiv.sym
    ; trans = Equiv.trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }

module Cones = Category Cones

private
  variable
    K K′ : Cone
    X : Obj
  module CM = Mor Cones
  module CI = IsoEquiv Cones

open CM using () renaming (_≅_ to _⇔_)
open CI using () renaming (_≃_ to _↮_)

cone-resp-iso : ∀ (κ : Cone) → Cone.N κ ≅ X → Σ[ κ′ ∈ Cone ] κ ⇔ κ′
cone-resp-iso {X = X} κ κ≅X = record
  { apex = record
    { ψ       = λ Y → Cone.ψ κ Y ∘ to
    ; commute = λ f → pullˡ (Cone.commute κ f)
    }
  } , record
  { from = record
    { arr     = from
    ; commute = cancelʳ isoˡ
    }
  ; to   = record
    { arr     = to
    ; commute = refl
    }
  ; iso  = record
    { isoˡ    = isoˡ
    ; isoʳ    = isoʳ
    }
  }
  where open _≅_ κ≅X
        open Cone
        open Apex
        open Equiv

iso-cone⇒iso-apex : K ⇔ K′ → N K ≅ N K′
iso-cone⇒iso-apex K⇔K′ = record
  { from = arr from
  ; to   = arr to
  ; iso  = record
    { isoˡ = isoˡ
    ; isoʳ = isoʳ
    }
  }
  where open _⇔_ K⇔K′


↮⇒-≃ : ∀ {i₁ i₂ : K ⇔ K′} → i₁ ↮ i₂ → iso-cone⇒iso-apex i₁ ≃ iso-cone⇒iso-apex i₂
↮⇒-≃ i₁↮i₂ = ⌞ from-≈ ⌟
  where open _↮_ i₁↮i₂
