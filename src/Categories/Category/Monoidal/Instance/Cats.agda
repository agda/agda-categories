{-# OPTIONS --without-K --safe #-}

-- The category of Cats is Monoidal

module Categories.Category.Monoidal.Instance.Cats where

open import Level

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.One using (One-⊤)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Product using (Product; πˡ; πʳ; _※_)
open import Categories.Category.Product.Properties using (project₁; project₂; unique)

-- Cats is a Monoidal Category with Product as Bifunctor
module Product {o ℓ e : Level} where
  private
    C = Cats o ℓ e

  Cats-has-all : BinaryProducts C
  Cats-has-all = record { product = λ {A} {B} → record
    { A×B = Product A B
    ; π₁ = πˡ
    ; π₂ = πʳ
    ; ⟨_,_⟩ = _※_
    ; project₁ = λ {_} {h} {i} → project₁ {i = h} {j = i}
    ; project₂ = λ {_} {h} {i} → project₂ {i = h} {j = i}
    ; unique = unique
    } }

  Cats-is : Cartesian C
  Cats-is = record { terminal = One-⊤ ; products = Cats-has-all }

  Cats-Monoidal : Monoidal C
  Cats-Monoidal = CartesianMonoidal.monoidal Cats-is
