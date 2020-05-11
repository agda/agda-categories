{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Topos {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Categories.Category.CartesianClosed C
open import Categories.Category.Complete.Finitely C
open import Categories.Diagram.Equalizer C
open import Categories.Diagram.SubobjectClassifier C

import Categories.Category.Complete.Finitely.Properties as Fₚ

open Category C

record Topos : Set (levelOfTerm C) where
  field
    cartesianClosed     : CartesianClosed
    subobjectClassifier : SubobjectClassifier
    equalizer           : ∀ {A B} (f g : A ⇒ B) → Equalizer f g

  finitelyComplete : FinitelyComplete
  finitelyComplete = record
    { cartesian = CartesianClosed.cartesian cartesianClosed
    ; equalizer = equalizer
    }

  open FinitelyComplete finitelyComplete using (module equalizer; pullback) public

  open Fₚ finitelyComplete using (finiteLimit) public
