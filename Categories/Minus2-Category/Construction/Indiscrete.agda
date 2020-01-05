{-# OPTIONS --without-K --safe #-}

-- An inhabited Indiscrete category is a -2-Category
module Categories.Minus2-Category.Construction.Indiscrete where

open import Level
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Minus2-Category
open import Categories.Category.Indiscrete
open import Categories.Morphism using (_≅_)

InhIndIs-2 : ∀ {o ℓ} → (X : Set o) → (x : X) → -2-Category {o} {ℓ} {ℓ}
InhIndIs-2 X x = record
  { cat = Indiscrete X
  ; Obj-Contr = x , λ y → record
    { from = lift tt
    ; to = lift tt
    ; iso = record
      { isoˡ = refl
      ; isoʳ = refl
      }
    }
  ; Hom-Conn = refl
  }
