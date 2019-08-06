{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Complete.Finitely {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Categories.Category.Cartesian C
open import Categories.Diagram.Equalizer C
open import Categories.Diagram.Pullback C

open Category C

record FinitelyComplete : Set (levelOfTerm C) where
  field
    cartesian : Cartesian
    equalizer : ∀ {A B} (f g : A ⇒ B) → Equalizer f g

  module cartesian = Cartesian cartesian
  module equalizer {A B} (f g : A ⇒ B) = Equalizer (equalizer f g)
  open cartesian public

  pullback : ∀ {X Y Z} (f : X ⇒ Z) (g : Y ⇒ Z) → Pullback f g
  pullback f g = Product×Equalizer⇒Pullback product (equalizer _ _)

  module pullback {X Y Z} (f : X ⇒ Z) (g : Y ⇒ Z) = Pullback (pullback f g)
