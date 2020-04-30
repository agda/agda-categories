{-# OPTIONS --without-K --safe #-}

module Data.Quiver where

-- A Quiver, also known as a multidigraph, is the "underlying graph" of
-- a category.

open import Level
open import Relation.Binary hiding (_⇒_)
import Relation.Binary.Reasoning.Setoid as EqR

-- a Quiver has vertices Obj and edges _⇒_, where edges form a setoid over _≈_.
record Quiver o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix 4 _≈_ _⇒_

  field
    Obj   : Set o
    _⇒_   : Rel Obj ℓ
    _≈_   : ∀ {A B} → Rel (A ⇒ B) e
    equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})

  setoid : {A B : Obj} → Setoid _ _
  setoid {A} {B} = record
    { Carrier       = A ⇒ B
    ; _≈_           = _≈_
    ; isEquivalence = equiv
    }

  module Equiv {A B : Obj} = IsEquivalence (equiv {A} {B})
  module EdgeReasoning {A B : Obj} = EqR (setoid {A} {B})
