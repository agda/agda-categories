{-# OPTIONS --without-K --safe #-}

module Categories.Category.Finite where

open import Level
open import Function.Inverse
import Data.Nat as ℕ
import Data.Fin as Fin
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as ≡

open import Categories.Category

FiniteSetoid : ∀ {c ℓ} n (S : Setoid c ℓ) → Set _
FiniteSetoid n S = Inverse (≡.setoid (Fin.Fin n)) S

record Finite {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  
  field
    ∣Obj∣ : ℕ.ℕ
    ∣_⇒_∣ : Obj → Obj → ℕ.ℕ

    Obj-finite : FiniteSetoid ∣Obj∣ (≡.setoid Obj)
    ⇒-finite   : ∀ A B → FiniteSetoid ∣ A ⇒ B ∣ (hom-setoid {A} {B})

  module Obj-finite   = Inverse Obj-finite
  module ⇒-finite A B = Inverse (⇒-finite A B)
