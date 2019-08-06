{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Cocomplete.Finitely {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Categories.Category.Cocartesian C
open import Categories.Diagram.Coequalizer C
open import Categories.Diagram.Pushout C
open import Categories.Diagram.Pushout.Properties C

open Category C

record FinitelyCocomplete : Set (levelOfTerm C) where
  field
    cocartesian : Cocartesian
    coequalizer : ∀ {A B} (f g : A ⇒ B) → Coequalizer f g

  module cocartesian = Cocartesian cocartesian
  module coequalizer {A B} (f g : A ⇒ B) = Coequalizer (coequalizer f g)
  open cocartesian public

  pushout : ∀ {X Y Z} (f : X ⇒ Y) (g : X ⇒ Z) → Pushout f g
  pushout f g = Coproduct×Coequalizer⇒Pushout coproduct (coequalizer _ _)

  module pushout {X Y Z} (f : X ⇒ Y) (g : X ⇒ Z) = Pushout (pushout f g)
