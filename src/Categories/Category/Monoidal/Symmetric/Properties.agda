{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Category.Monoidal.Symmetric.Properties
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (SM : Symmetric M) where

import Categories.Category.Monoidal.Braided.Properties as BraidedProperties

open import Categories.Category.Monoidal.Properties M using (monoidal-Op)
open import Categories.Morphism.Reasoning C
open import Data.Product using (_,_)

open Category C
open HomReasoning
open Symmetric SM

-- Shorthands for the braiding

open BraidedProperties braided public using (module Shorthands)

-- Extra properties of the braiding in a symmetric monoidal category

braiding-selfInverse : ∀ {X Y} → braiding.⇐.η (X , Y) ≈ braiding.⇒.η (Y , X)
braiding-selfInverse = introʳ commutative ○ cancelˡ (braiding.iso.isoˡ _)

inv-commutative : ∀ {X Y} → braiding.⇐.η (X , Y) ∘ braiding.⇐.η (Y , X) ≈ id
inv-commutative = ∘-resp-≈ braiding-selfInverse braiding-selfInverse ○ commutative

-- The opposite monoidal category is symmetric

open BraidedProperties braided using (braided-Op)

symmetric-Op : Symmetric monoidal-Op
symmetric-Op = record
    { braided = braided-Op
    ; commutative = inv-commutative
    }
