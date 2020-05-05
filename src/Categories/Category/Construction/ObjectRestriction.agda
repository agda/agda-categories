{-# OPTIONS --without-K --safe #-}

-- Given a predicate on the objects of a Category C, build another category
-- with just those that satisfy a pr

module Categories.Category.Construction.ObjectRestriction where

open import Level
open import Data.Product using (Σ; proj₁)
open import Relation.Unary using (Pred)
open import Function using (_on_) renaming (id to id→)

open import Categories.Category.Core

private
  variable
    o ℓ e ℓ′ : Level

ObjectRestriction : (C : Category o ℓ e) → Pred (Category.Obj C) ℓ′ → Category (o ⊔ ℓ′) ℓ e
ObjectRestriction C R = record
  { Obj = Σ Obj R
  ; _⇒_ = _⇒_ on proj₁
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = equiv
  ; ∘-resp-≈ = ∘-resp-≈
  }
  where open Category C
