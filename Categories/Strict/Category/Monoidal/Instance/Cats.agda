{-# OPTIONS --without-K --safe #-}

-- The category of Strict Categories is (Strict) Monoidal

module Categories.Strict.Category.Monoidal.Instance.Cats where

open import Level
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry)

open import Categories.Strict.Category
open import Categories.Strict.Category.Instance.Cats
open import Categories.Category.Monoidal
open import Categories.Strict.Functor.Bifunctor
open import Categories.Strict.Category.Instance.One
open import Categories.Strict.Category.Product
open import Categories.Strict.Category.Product.Properties
import Categories.Category.Cartesian as Cartesian

-- Cats is a Monoidal Category with Product as Bifunctor
module Product {o ℓ : Level} where
  private
    C = Cats o ℓ
    open Cartesian C

  Cats-has-all : BinaryProducts
  Cats-has-all = record { product = λ {A} {B} → record
    { A×B = Product A B
    ; π₁ = πˡ
    ; π₂ = πʳ
    ; ⟨_,_⟩ = _※_
    ; project₁ = λ {_} {h} {i} → project₁ {i = h} {j = i}
    ; project₂ = λ {_} {h} {i} → project₂ {i = h} {j = i}
    ; unique =   λ {_} {h} {i} {j} x y → unique {i = i} {j} {h} x y
    } }

  Cats-is : Cartesian
  Cats-is = record { terminal =  One-⊤ ; products = Cats-has-all }

  private
    module Cart = Cartesian.Cartesian Cats-is

  Cats-Monoidal : Monoidal C
  Cats-Monoidal = Cart.monoidal
