{-# OPTIONS --without-K --safe #-}
open import Categories.Category using (Category; module Definitions)

-- Definition of the Arrow Category of a Category C
module Categories.Category.Construction.Arrow {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Product using (_,_; _×_; map; zip)
open import Function.Base using (_$_)
open import Relation.Binary.Core using (Rel)

import Categories.Morphism as M
open M C
open import Categories.Morphism.Reasoning C

open Category C
open Definitions C
open HomReasoning

private
  variable
    A B D E : Obj

record Morphism : Set (o ⊔ ℓ) where
  field
    {dom} : Obj
    {cod} : Obj
    arr   : dom ⇒ cod

record Morphism⇒ (f g : Morphism) : Set (ℓ ⊔ e) where
  constructor mor⇒
  private
    module f = Morphism f
    module g = Morphism g

  field
    {dom⇒} : f.dom ⇒ g.dom
    {cod⇒} : f.cod ⇒ g.cod
    square : CommutativeSquare f.arr dom⇒ cod⇒ g.arr

Arrow : Category _ _ _
Arrow = record
  { Obj       = Morphism
  ; _⇒_       = Morphism⇒
  ; _≈_       = λ f g → dom⇒ f ≈ dom⇒ g × cod⇒ f ≈ cod⇒ g
  ; id        = mor⇒ $ identityˡ ○ ⟺ identityʳ
  ; _∘_       = λ m₁ m₂ → mor⇒ $ glue (square m₁) (square m₂)
  ; assoc     = assoc , assoc
  ; sym-assoc = sym-assoc , sym-assoc
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; identity² = identity² , identity²
  ; equiv     = record
    { refl  = refl , refl
    ; sym   = map sym sym
    ; trans = zip trans trans
    }
  ; ∘-resp-≈  = zip ∘-resp-≈ ∘-resp-≈
  }
  where
  open Morphism⇒
  open Equiv

private
  module MM = M Arrow

module _ where
  open _≅_
  open Equiv

  lift-iso : ∀ {f h} →
               (iso₁ : A ≅ D) → (iso₂ : B ≅ E) →
               CommutativeSquare f (from iso₁) (from iso₂) h →
               record { arr = f } MM.≅ record { arr = h }
  lift-iso {f = f} {h = h} iso₁ iso₂ sq = record
    { from = record { square = sq }
    ; to   = record { square = begin
      to iso₂ ∘ h                           ≈⟨ introʳ (isoʳ iso₁) ⟩
      (to iso₂ ∘ h) ∘ from iso₁ ∘ to iso₁   ≈⟨ assoc ⟩
      to iso₂ ∘ h ∘ from iso₁ ∘ to iso₁     ≈˘⟨ refl ⟩∘⟨ pushˡ sq ⟩
      to iso₂ ∘ (from iso₂ ∘ f) ∘ to iso₁   ≈⟨ sym-assoc ⟩
      (to iso₂ ∘ (from iso₂ ∘ f)) ∘ to iso₁ ≈⟨ cancelˡ (isoˡ iso₂) ⟩∘⟨ refl ⟩
      f ∘ to iso₁                           ∎ }
    ; iso  = record
      { isoˡ = isoˡ iso₁ , isoˡ iso₂
      ; isoʳ = isoʳ iso₁ , isoʳ iso₂
      }
    }
