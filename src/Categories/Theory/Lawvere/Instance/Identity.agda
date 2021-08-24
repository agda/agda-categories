{-# OPTIONS --without-K --safe #-}

-- The 'Identity' instance, with all of Setoids as models

module Categories.Theory.Lawvere.Instance.Identity where

open import Data.Fin using (splitAt)
open import Data.Sum using ([_,_]′)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; isEquivalence)

open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Nat
open import Categories.Category.Unbundled.Properties using (unpack′)
open import Categories.Functor.IdentityOnObjects using (id-IOO)
open import Categories.Object.Product using (Product)
open import Categories.Theory.Lawvere using (LawvereTheory)

Identity : LawvereTheory 0ℓ 0ℓ
Identity = record
  { L = unpack′ (Category.op Nat)
  ; T = CartesianCategory.cartesian Natop-Cartesian
  ; I = id-IOO
  ; CartF = record
    { F-resp-⊤ = record { ! = λ () ; !-unique = λ _ () }
    ; F-resp-× = λ {m} {n} → record { P m n }
    }
  }
  where
  module P m n = Product Natop (Natop-Product m n)
