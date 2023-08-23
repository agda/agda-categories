{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Object.Terminal hiding (up-to-iso)
open import Categories.Category.CartesianClosed.Bundle
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Category.Cocartesian
open import Categories.Category.CartesianClosed
open import Categories.Object.NaturalNumber.Properties.F-Algebras

module Categories.Object.NaturalNumber.Properties.CCC {o ℓ e} (CCC : CartesianClosedCategory o ℓ e) (𝒞-Coproducts : BinaryCoproducts (CartesianClosedCategory.U CCC)) where

open import Level

open CartesianClosedCategory CCC renaming (U to 𝒞)
open CartesianClosed cartesianClosed
open Cartesian cartesian
open BinaryProducts products

open import Categories.Object.NaturalNumber 𝒞 terminal
open import Categories.Object.NaturalNumber.Parametrized cartesianCategory
open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open HomReasoning
open Equiv

open Terminal terminal

NNO×CCC⇒PNNO : NaturalNumber → ParametrizedNaturalNumber
NNO×CCC⇒PNNO nno = Initial⇒PNNO cartesianCategory 𝒞-Coproducts (NNO⇒Initial 𝒞 terminal 𝒞-Coproducts nno) λ A → record 
  { ! = λ {X} → record { f = {!   !} ; commutes = {!   !} } 
  ; !-unique = {!   !} 
  }
  where
    open NaturalNumber nno