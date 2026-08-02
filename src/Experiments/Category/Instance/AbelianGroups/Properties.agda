{-# OPTIONS --without-K --safe #-}
module Experiments.Category.Instance.AbelianGroups.Properties where

open import Level
open import Data.Unit.Polymorphic
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)

import Algebra.Construct.DirectProduct as DirectProduct
open import Algebra.Properties.AbelianGroup

import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Object.Zero
open import Categories.Object.Biproduct
open import Categories.Object.Kernel
open import Categories.Object.Cokernel

open import Experiments.Category.Instance.AbelianGroups

open import Categories.Category.Preadditive
open import Categories.Category.Additive
open import Experiments.Category.PreAbelian

import Categories.Morphism.Reasoning as MR

private
  variable
    c ℓ : Level

open AbelianGroup
open AbelianGroupHomomorphism

