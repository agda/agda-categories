{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Complete.Finitely {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Categories.Category.BinaryProducts C using (BinaryProducts)
open import Categories.Category.Cartesian C using (Cartesian)
open import Categories.Diagram.Equalizer C using (Equalizer)
open import Categories.Diagram.Pullback C using (Pullback; Product×Equalizer⇒Pullback)

open Category C

record FinitelyComplete : Set (levelOfTerm C) where
  field
    cartesian : Cartesian
    equalizer : ∀ {A B} (f g : A ⇒ B) → Equalizer f g

  module equalizer {A B} (f g : A ⇒ B) = Equalizer (equalizer f g)
  open Cartesian cartesian using (products)

  pullback : ∀ {X Y Z} (f : X ⇒ Z) (g : Y ⇒ Z) → Pullback f g
  pullback f g = Product×Equalizer⇒Pullback (BinaryProducts.product products) (equalizer _ _)

  module pullback {X Y Z} (f : X ⇒ Z) (g : Y ⇒ Z) = Pullback (pullback f g)
