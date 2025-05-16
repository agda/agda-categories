{-# OPTIONS --without-K --safe #-}

-- The category of Sets is Monoidal

module Categories.Category.Monoidal.Instance.Sets where

open import Level
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry; map; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality.Core
open import Function.Related.TypeIsomorphisms
open import Function using (_$_)

open import Categories.Category.BinaryProducts using (BinaryProducts)
import Categories.Category.Cartesian as Cartesian
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
import Categories.Category.Cocartesian as Cocartesian
open import Categories.Category.Instance.EmptySet
open import Categories.Category.Instance.Sets
open import Categories.Category.Instance.SingletonSet
import Categories.Morphism as Morphism
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Functor.Bifunctor using (Bifunctor)

open import Data.Sum.Properties

-- Sets is a Monoidal Category with × as Bifunctor
module Product {o : Level} where
  private
    S = Sets o
    open Cartesian S

  Sets-has-all : BinaryProducts S
  Sets-has-all = record { product = λ {A} {B} → record
    { A×B = A × B
    ; π₁ = proj₁
    ; π₂ = proj₂
    ; ⟨_,_⟩ = <_,_>
    ; project₁ = λ _ → refl
    ; project₂ = λ _ → refl
    ; unique = λ p₁ p₂ x → sym (cong₂ _,_ (p₁ x) (p₂ x))
    } }

  Sets-is : Cartesian
  Sets-is = record { terminal = SingletonSet-⊤ ; products = Sets-has-all }

  Sets-Monoidal : Monoidal S
  Sets-Monoidal = CartesianMonoidal.monoidal Sets-is

module Coproduct {o : Level} where
  private
    S = Sets o
    open Cocartesian S

  Sets-has-all : BinaryCoproducts
  Sets-has-all = record { coproduct = λ {A} {B} → record
    { A+B = A ⊎ B
    ; i₁ = inj₁
    ; i₂ = inj₂
    ; [_,_] = [_,_]′
    ; inject₁ = λ _ → refl
    ; inject₂ = λ _ → refl
    ; unique = λ { i₁ i₂ (inj₁ x) → sym (i₁ x) ; i₁ i₂ (inj₂ y) → sym (i₂ y)} -- stdlib?
    } }

  Sets-is : Cocartesian
  Sets-is = record { initial = EmptySet-⊥ ; coproducts = Sets-has-all }

  Sets-Monoidal : Monoidal S
  Sets-Monoidal = Cocartesian.CocartesianMonoidal.+-monoidal S Sets-is
