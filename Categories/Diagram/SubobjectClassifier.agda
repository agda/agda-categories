{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- the usual notion requires C to have finite limits.
-- this definition is a generalization by omitting that requirement as the definition
-- itself does not involve any limit.
module Categories.Diagram.SubobjectClassifier {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

open import Categories.Object.Terminal C
open import Categories.Morphism C
open import Categories.Diagram.Pullback C

record SubobjectClassifier : Set (o ⊔ ℓ ⊔ e) where
  field
    Ω        : Obj
    terminal : Terminal

  module terminal = Terminal terminal
  open terminal

  field
    true      : ⊤ ⇒ Ω
    universal : ∀ {X Y} {f : X ⇒ Y} → Mono f → Y ⇒ Ω
    pullback  : ∀ {X Y} {f : X ⇒ Y} {mono : Mono f} → Pullback (universal mono) true
    unique    : ∀ {X Y} {f : X ⇒ Y} {g} {mono : Mono f} → Pullback g true → universal mono ≈ g
