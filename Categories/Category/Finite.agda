{-# OPTIONS --without-K --safe #-}

module Categories.Category.Finite where

open import Level
open import Data.Product using (Σ; _,_; ∃₂)
open import Function.Equality using (Π; _⟶_)
open import Function.Inverse
open import Data.Nat as ℕ hiding (_⊔_)
import Data.Fin as Fin
open import Data.Vec as Vec
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as ≡

open import Categories.Category
open Π

FiniteSetoid : ∀ {c ℓ} n (S : Setoid c ℓ) → Set _
FiniteSetoid n S = Inverse (≡.setoid (Fin.Fin n)) S

record Finite {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  
  field
    ∣Obj∣ : ℕ
    ∣_⇒_∣ : Obj → Obj → ℕ

    Obj-finite : FiniteSetoid ∣Obj∣ (≡.setoid Obj)
    ⇒-finite   : ∀ A B → FiniteSetoid ∣ A ⇒ B ∣ (hom-setoid {A} {B})

  module Obj-finite   = Inverse Obj-finite
  module ⇒-finite A B = Inverse (⇒-finite A B)

  private
    Fins : ∀ n → Vec (Fin.Fin n) n
    Fins ℕ.zero    = []
    Fins (ℕ.suc n) = Fin.fromℕ n ∷ Vec.map (Fin.raise 1) (Fins n)

  -- enumeration of all objects
  Objs : Vec Obj ∣Obj∣
  Objs = Vec.map (Obj-finite.to ⟨$⟩_) (Fins ∣Obj∣)

  private
    ObjPairs : ∀ {a} {A : Set a} → (Obj → Obj → A) → Vec A (∣Obj∣ * ∣Obj∣)
    ObjPairs {_} {A} f = Objs >>= ap
      where ap : Obj → Vec A ∣Obj∣
            ap X = Vec.map (f X) Objs

  -- enumeration of all morphisms of a given pair of objects
  ⟦_⇒_⟧ : ∀ A B → Vec (A ⇒ B) ∣ A ⇒ B ∣
  ⟦ A ⇒ B ⟧ = Vec.map (⇒-finite.to A B ⟨$⟩_) (Fins ∣ A ⇒ B ∣)

  -- number of all morphisms
  ∣-⇒-| : ℕ
  ∣-⇒-| = foldr (λ _ → ℕ) _+_ 0 (ObjPairs ∣_⇒_∣)
