{-# OPTIONS --without-K --safe #-}

-- Any category can be made into a trivial restriction category

module Categories.Category.Restriction.Construction.Trivial where

open import Level using (Level)

open import Categories.Category.Core using (Category)
open import Categories.Category.Restriction using (Restriction)
open import Categories.Morphism.Reasoning.Core using (id-comm-sym)

private
  variable
     o ℓ e : Level

Trivial : (C : Category o ℓ e) → Restriction C
Trivial C = record
  { _↓ = λ _ → id
  ; pidʳ = identityʳ
  ; ↓-comm = Equiv.refl
  ; ↓-denestʳ = Equiv.sym identity²
  ; ↓-skew-comm = id-comm-sym C
  ; ↓-cong = λ _ → Equiv.refl
  }
  where open Category C
