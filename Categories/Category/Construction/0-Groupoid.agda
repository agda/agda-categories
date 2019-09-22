{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

-- Lifts a setoid into a 1-groupoid

module Categories.Category.Construction.0-Groupoid
  {c ℓ} e (S : Setoid c ℓ) where

open import Level using (Lift)
open import Data.Unit using (⊤)
open import Function using (flip)

open import Categories.Category.Groupoid using (Groupoid)

open Setoid S

0-Groupoid : Groupoid c ℓ e
0-Groupoid = record
  { category = record
    { Obj = Carrier
    ; _⇒_ = _≈_
    ; _≈_ = λ _ _ → Lift e ⊤
    ; id  = refl
    ; _∘_ = flip trans
    }
  ; isGroupoid = record { _⁻¹ = sym }
  }
