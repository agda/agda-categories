{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor

-- Cartesian fibration, also known as Grothendieck Fibration, see
-- https://ncatlab.org/nlab/show/Grothendieck+fibration
module Categories.Functor.Fibration {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F : Functor C D) where

open import Level

open import Categories.Morphism D using (_≅_)
open import Categories.Morphism.Cartesian using (Cartesian)

private
  module C = Category C
  module D = Category D
  open Functor F

record Fibration : Set (levelOfTerm F) where
  field
    universal₀ : ∀ {A B} (f : A D.⇒ F₀ B) → C.Obj
    universal₁ : ∀ {A B} (f : A D.⇒ F₀ B) → universal₀ f C.⇒ B
    iso        : ∀ {A B} (f : A D.⇒ F₀ B) → F₀ (universal₀ f) ≅ A

  module iso {A B} (f : A D.⇒ F₀ B) = _≅_ (iso f)

  field
    commute   : ∀ {A B} (f : A D.⇒ F₀ B) → f D.∘ iso.from f D.≈ F₁ (universal₁ f)
    cartesian : ∀ {A B} (f : A D.⇒ F₀ B) → Cartesian F (universal₁ f)

  module cartesian {A B} (f : A D.⇒ F₀ B) = Cartesian (cartesian f)
