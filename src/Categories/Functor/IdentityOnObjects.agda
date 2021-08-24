{-# OPTIONS --without-K --safe #-}


-- Identity-on-Objects Functor for (Object-)Unbundled Categories

module Categories.Functor.IdentityOnObjects where

open import Data.Product using (_,_)
open import Function using () renaming (id to id→)
open import Level

open import Categories.Category.Unbundled using (Category)
open import Categories.Category.Unbundled.Properties using (pack′)
open import Categories.Category.Unbundled.Utilities using (module Equiv)
open import Categories.Functor.Core using (Functor)

private
  variable
    o ℓ e ℓ′ e′ : Level

record IdentityOnObjects {Obj : Set o} (C : Category Obj ℓ e) (D : Category Obj ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ ℓ′ ⊔ e′) where
  eta-equality
  private module C = Category C
  private module D = Category D

  field
    F₁ : ∀ {A B} → (A C.⇒ B) → A D.⇒ B

    identity     : ∀ {A} → F₁ (C.id {A}) D.≈ D.id
    homomorphism : ∀ {X Y Z} {f : X C.⇒ Y} {g : Y C.⇒ Z} →
                     F₁ (g C.∘ f) D.≈ F₁ g D.∘ F₁ f
    F-resp-≈     : ∀ {A B} {f g : A C.⇒ B} → f C.≈ g → F₁ f D.≈ F₁ g

IOO⇒Functor : {Ob : Set o} {C : Category Ob ℓ e} {D : Category Ob ℓ′ e′} →
  (F : IdentityOnObjects C D) → Functor (pack′ C) (pack′ D)
IOO⇒Functor F = record { F₀ = id→; IOO }
  where module IOO = IdentityOnObjects F

id-IOO : {Obj : Set o} {C : Category Obj ℓ e} → IdentityOnObjects C C
id-IOO {C = C} = record { F₁ = id→ ; identity = refl ; homomorphism = refl ; F-resp-≈ = id→ }
  where open Equiv C
