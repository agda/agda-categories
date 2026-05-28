{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

-- Defines the following properties of a Category:
-- Cocartesian -- a Cocartesian category is a category with all coproducts

-- Most of the work is dual to Categories.Category.Cartesian, so the idea
-- in this module is to make use of duality

module Categories.Category.Cocartesian {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (levelOfTerm)
open import Data.Nat using (ℕ; suc)


private
  module 𝒞 = Category 𝒞
  open 𝒞
  variable
    A : Obj

open import Categories.Category.BinaryCoproducts 𝒞
open import Categories.Category.Cartesian 𝒞.op
open import Categories.Object.Initial 𝒞 using (Initial)
open import Categories.Object.Duality 𝒞

record Cocartesian : Set (levelOfTerm 𝒞) where
  field
    initial    : Initial
    coproducts : BinaryCoproducts

  open Initial initial
    renaming (! to ¡; !-unique to ¡-unique; !-unique₂ to ¡-unique₂)
    public
  open BinaryCoproducts coproducts hiding (module Dual) public

  times : Obj → ℕ → Obj
  times A 0 = Initial.⊥ initial
  times A 1 = A
  times A (suc (suc n)) = A + times A (suc n)

  module Dual where
    open BinaryCoproducts.Dual coproducts public

    op-cartesian : Cartesian
    op-cartesian = record
      { terminal = ⊥⇒op⊤ initial
      ; products = op-binaryProducts
      }

    module op-cartesian = Cartesian op-cartesian
