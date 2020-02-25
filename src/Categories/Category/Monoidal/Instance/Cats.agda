{-# OPTIONS --without-K --safe #-}

-- The category of Cats is Monoidal

module Categories.Category.Monoidal.Instance.Cats where

open import Level
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry)

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Instance.Cats
open import Categories.Category.Monoidal
open import Categories.Functor.Bifunctor
open import Categories.Category.Instance.One
open import Categories.Category.Product
open import Categories.Category.Product.Properties
import Categories.Category.Cartesian as Cartesian
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

-- Cats is a Monoidal Category with Product as Bifunctor
module Product {o ℓ e : Level} where
  private
    C = Cats o ℓ e
    open Cartesian C

  Cats-has-all : BinaryProducts
  Cats-has-all = record { product = λ {A} {B} → record
    { A×B = Product A B
    ; π₁ = πˡ
    ; π₂ = πʳ
    ; ⟨_,_⟩ = _※_
    ; project₁ = λ {_} {h} {i} → project₁ {i = h} {j = i}
    ; project₂ = λ {_} {h} {i} → project₂ {i = h} {j = i}
    ; unique = unique
    } }

  Cats-is : Cartesian
  Cats-is = record { terminal = One-⊤ ; products = Cats-has-all }

  private
    module Cart = Cartesian.Cartesian Cats-is

  Cats-Monoidal : Monoidal C
  Cats-Monoidal = Cart.monoidal
