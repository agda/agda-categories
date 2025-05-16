{-# OPTIONS --without-K --safe #-}

{-
  Extremal Mono and Epimorphisms.

  https://ncatlab.org/nlab/show/extremal+epimorphism
-}

open import Categories.Category.Core

module Categories.Morphism.Extremal {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Categories.Morphism 𝒞

open Category 𝒞

IsExtremalEpi : ∀ {A B} {f : A ⇒ B} → Epi f → Set (o ⊔ ℓ ⊔ e)
IsExtremalEpi {A = A} {B = B} {f = f} epi =
  ∀ {X} {i : X ⇒ B} {g : A ⇒ X} → Mono i → f ≈ i ∘ g → IsIso i

IsExtremalMono : ∀ {A B} {f : A ⇒ B} → Mono f → Set (o ⊔ ℓ ⊔ e)
IsExtremalMono {A = A} {B = B} {f = f} mono =
  ∀ {X} {g : X ⇒ B} {i : A ⇒ X} → Epi i → f ≈ g ∘ i → IsIso i

record ExtremalEpi {A B} (f : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    epi : Epi f
    extremal : IsExtremalEpi epi


record ExtremalMono {A B} (f : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    mono : Mono f
    extremal : IsExtremalMono mono
