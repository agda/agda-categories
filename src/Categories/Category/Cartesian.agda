{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

-- Defines the following properties of a Category:
-- Cartesian -- a Cartesian category is a category with all products

--  (for the induced Monoidal structure, see Cartesian.Monoidal)

module Categories.Category.Cartesian {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (levelOfTerm)
open import Data.Nat using (ℕ; suc)

open import Categories.Category.BinaryProducts 𝒞 using (BinaryProducts; module BinaryProducts)
open import Categories.Object.Terminal 𝒞 using (Terminal)

private
  open Category 𝒞
  variable
    A : Obj

-- Cartesian monoidal category
record Cartesian : Set (levelOfTerm 𝒞) where
  field
    terminal : Terminal
    products : BinaryProducts
  
  open Terminal terminal public
  open BinaryProducts products public

  power : Obj → ℕ → Obj
  power A 0 = Terminal.⊤ terminal
  power A 1 = A
  power A (suc (suc n)) = A × power A (suc n)
