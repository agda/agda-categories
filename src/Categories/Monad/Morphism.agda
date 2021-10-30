{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Monad

module Categories.Monad.Morphism {o ℓ e} {C D : Category o ℓ e} (M : Monad C) (N : Monad D) where

open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Equivalence
open import Categories.Functor

private
  module M = Monad M

open NaturalTransformation

-- monad morphism in the sense of the nLab
-- https://ncatlab.org/nlab/show/monad#the_bicategory_of_monads
-- between generic monads t : a -> a & s : b -> b
-- TODO
record Monad⇒ (M : Monad C) (N : Monad D) : Set (o ⊔ ℓ ⊔ e) where
  field
    X : Functor C D
    α : NaturalTransformation (Monad.F N ∘F X) (X ∘F Monad.F M)
    -- todo: properties


-- monad morphism in the sense of [ref],
-- monads are on the same category
-- TODO
