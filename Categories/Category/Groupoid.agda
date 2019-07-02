{-# OPTIONS --without-K --safe #-}
module Categories.Category.Groupoid where

open import Level

open import Categories.Category
import Categories.Morphism

record Groupoid {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  private
    module C = Category C
  open C public

  open Categories.Morphism C

  infix 10 _⁻¹
  
  field
    _⁻¹ : ∀ {A B} → A ⇒ B → B ⇒ A
    iso : ∀ {A B} {f : A ⇒ B} → Iso f (f ⁻¹)

  equiv-obj : ∀ {A B} → A ⇒ B → A ≅ B
  equiv-obj f = record
    { from = f
    ; to   = _
    ; iso  = iso
    }

  equiv-obj′ : ∀ {A B} → A ⇒ B → B ≅ A
  equiv-obj′ f = record
    { from = f ⁻¹
    ; to   = f
    ; iso  = record
      { isoˡ = isoʳ
      ; isoʳ = isoˡ
      }
    }
    where open Iso (iso {f = f})
