{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal

module Categories.Category.Monoidal.Closed {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

private
  module C = Category C
  open Category C

  variable
    X : Obj

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Adjoint
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Category.Monoidal.Properties M
open import Categories.Morphism C
open import Categories.Morphism.Properties C
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.NaturalTransformation.Dinatural using (extranaturalʳ)
import Categories.Category.Closed as Cl

record Closed : Set (levelOfTerm M) where
  open Monoidal M

  field
    [-,-]   : Bifunctor C.op C C 
    adjoint : (-⊗ X) ⊣ appˡ [-,-] X
    
  module adjoint {X} = Adjoint (adjoint {X})
  module [-,-] = Functor [-,-]

  -- TODO: show that closed monoidal category is closed.
