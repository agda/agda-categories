{-# OPTIONS --without-K --safe #-}

-- The category of Sets is Monoidal

module Categories.Category.Monoidal.Instance.Sets where

open import Level
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry; map; <_,_>)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality
open import Function.Inverse using (module Inverse; _↔_)
open import Function.Related.TypeIsomorphisms
open import Function.Equality using () renaming (_⟨$⟩_ to fun)
open import Function using (_$_)

open import Categories.Category.Instance.Sets
open import Categories.Category.Monoidal
open import Categories.Functor.Bifunctor
open import Categories.Category.Instance.SingletonSet
import Categories.Morphism as Morphism
import Categories.Category.Cartesian as Cartesian

-- Sets is a Monoidal Category with × as Bifunctor
module Product {o : Level} where
  private
    S = Sets o
    open Cartesian S

  Sets-has-all : BinaryProducts
  Sets-has-all = record { product = λ {A} {B} → record
    { A×B = A × B
    ; π₁ = proj₁
    ; π₂ = proj₂
    ; ⟨_,_⟩ = <_,_>
    ; project₁ = refl
    ; project₂ = refl
    ; unique = λ p₁ p₂ {x} → sym (cong₂ _,_ (p₁ {x}) (p₂ {x}))
    } }

  Sets-is : Cartesian
  Sets-is = record { terminal = SingletonSet-⊤ ; products = Sets-has-all }

  private
    module Cart = Cartesian.Cartesian Sets-is

  Sets-Monoidal : Monoidal S
  Sets-Monoidal = Cart.monoidal

-- TODO: Sets is a Monoidal Category with ⊎ as Bifunctor
