{-# OPTIONS --without-K --safe #-}
module Categories.Category.Groupoid where

open import Level using (Level; suc; _⊔_)

open import Categories.Category
import Categories.Morphism

record IsGroupoid {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C public
  open Definitions C public

  open Categories.Morphism C

  infix 10 _⁻¹

  field
    _⁻¹ : ∀ {A B} → A ⇒ B → B ⇒ A
    iso : ∀ {A B} {f : A ⇒ B} → Iso f (f ⁻¹)

  module iso {A B f} = Iso (iso {A} {B} {f})

  equiv-obj : ∀ {A B} → A ⇒ B → A ≅ B
  equiv-obj f = record
    { from = f
    ; to   = _
    ; iso  = iso
    }

  -- this definition doesn't seem to 'carry its weight'
  equiv-obj-sym : ∀ {A B} → A ⇒ B → B ≅ A
  equiv-obj-sym f = ≅.sym (equiv-obj f)

-- A groupoid is a category that has a groupoid structure

record Groupoid (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    category   : Category o ℓ e
    isGroupoid : IsGroupoid category

  open IsGroupoid isGroupoid public
