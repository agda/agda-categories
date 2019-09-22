{-# OPTIONS --without-K --safe #-}
module Categories.Category.IsGroupoid where

open import Level

open import Categories.Category
import Categories.Morphism

record IsGroupoid {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C public

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
