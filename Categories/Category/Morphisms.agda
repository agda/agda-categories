{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Category.Morphisms {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Product using (_,_; _×_; map; zip)
open import Relation.Binary using (Rel)

import Categories.Morphism as M
open M C
open import Categories.Square C

open Category C hiding (dom; cod)
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
  private
    module f = Morphism f
    module g = Morphism g

  field
    {dom⇒} : f.dom ⇒ g.dom
    {cod⇒} : f.cod ⇒ g.cod
    square : CommutativeSquare f.arr dom⇒ cod⇒ g.arr

Morphisms : Category _ _ _
Morphisms = record
  { Obj       = Morphism
  ; _⇒_       = Morphism⇒
  ; _≈_       = _≈′_
  ; id        = record { square = trans identityˡ (sym identityʳ) }
  ; _∘_       = _∘′_
  ; assoc     = assoc , assoc
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; equiv     = record
    { refl  = refl , refl
    ; sym   = map sym sym
    ; trans = zip trans trans
    }
  ; ∘-resp-≈  = zip ∘-resp-≈ ∘-resp-≈
  }
  where _≈′_ : ∀ {f g} → Rel (Morphism⇒ f g) _
        f ≈′ g = f.dom⇒ ≈ g.dom⇒ × f.cod⇒ ≈ g.cod⇒
          where module f = Morphism⇒ f
                module g = Morphism⇒ g
                
        _∘′_ : ∀ {f g h} → Morphism⇒ g h → Morphism⇒ f g → Morphism⇒ f h
        m₁ ∘′ m₂ = record
          { square = glue m₁.square m₂.square
          }
          where module m₁ = Morphism⇒ m₁
                module m₂ = Morphism⇒ m₂

private
  module MM = M Morphisms

module _ where
  open _≅_
    
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
      to iso₂ ∘ (from iso₂ ∘ f) ∘ to iso₁   ≈˘⟨ assoc ⟩
      (to iso₂ ∘ (from iso₂ ∘ f)) ∘ to iso₁ ≈⟨ cancelˡ (isoˡ iso₂) ⟩∘⟨ refl ⟩
      f ∘ to iso₁                           ∎ }
    ; iso  = record
      { isoˡ = isoˡ iso₁ , isoˡ iso₂
      ; isoʳ = isoʳ iso₁ , isoʳ iso₂
      }
    }

  
