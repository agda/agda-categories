{-# OPTIONS --without-K --safe #-}
module Categories.Category.Discrete where

-- Discrete Category.
-- https://ncatlab.org/nlab/show/discrete+category
-- says:
-- A category is discrete if it is both a groupoid and a preorder. That is,
-- every morphism should be invertible, any two parallel morphisms should be equal.
-- The idea is that in a discrete category, no two distinct (nonisomorphic) objects
-- are connectable by any path (morphism), and an object connects to itself only through
-- its identity morphism.

open import Level using (Level; suc; _⊔_)

open import Categories.Category using (Category)
open import Categories.Category.Groupoid using (IsGroupoid)

record IsDiscrete {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C using (Obj; _⇒_; _≈_)
  field
     isGroupoid : IsGroupoid C
     preorder : {A B : Obj} → (f g : A ⇒ B) → f ≈ g

record DiscreteCategory (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    category   : Category o ℓ e
    isDiscrete : IsDiscrete category

  open IsDiscrete isDiscrete public
