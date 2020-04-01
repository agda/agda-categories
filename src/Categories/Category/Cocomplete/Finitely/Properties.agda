{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Cocomplete.Finitely

module Categories.Category.Cocomplete.Finitely.Properties {o ℓ e} {C : Category o ℓ e} (finite : FinitelyCocomplete C) where

open import Categories.Category.Duality C
private
  module C = Category C
  open C

open import Categories.Category.Finite.Fin
open import Categories.Category.Complete.Finitely C.op
open import Categories.Category.Complete.Finitely.Properties (FinitelyCocomplete⇒coFinitelyComplete finite)

open import Categories.Diagram.Colimit
open import Categories.Diagram.Limit
open import Categories.Diagram.Duality C
open import Categories.Functor

finiteColimit : (shape : FinCatShape) (F : Functor (FinCategory shape) C) → Colimit F
finiteColimit shape F = coLimit⇒Colimit (finiteLimit shape.op F.op)
  where module shape = FinCatShape shape
        module F = Functor F
