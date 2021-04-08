{-# OPTIONS --without-K --safe #-}

-- The Category of Algebraic Kan Complexes
module Categories.Category.Instance.KanComplexes where

open import Level

open import Function using (_$_)
open import Data.Product using (Σ; _,_; proj₁)

open import Categories.Category
open import Categories.Category.SubCategory
open import Categories.Category.Instance.SimplicialSet

import Categories.Category.Instance.SimplicialSet.Properties as ΔSetₚ

module _ (o ℓ : Level) where
  open Category (SimplicialSet o ℓ)
  open ΔSetₚ o ℓ
  open IsKanComplex
  open Equiv
  
  -- As we are working with Algebraic Kan Complexes, maps between two Kan Complexes ought
  -- to take the chosen filler in 'X' to the chosen filler in 'Y'.
  PreservesFiller : ∀ {X Y : ΔSet} → IsKanComplex X → IsKanComplex Y → (X ⇒ Y) → Set (o ⊔ ℓ)
  PreservesFiller {X} {Y} X-Kan Y-Kan f = ∀ {n} {k} → (i : Λ[ n , k ] ⇒ X) → (f ∘ filler X-Kan {n} i) ≈ filler Y-Kan (f ∘ i)  

  KanComplexes : Category (suc o ⊔ suc ℓ) (o ⊔ ℓ ⊔ (o ⊔ ℓ)) (o ⊔ ℓ)
  KanComplexes = SubCategory (SimplicialSet o ℓ) {I = Σ ΔSet IsKanComplex} $ record
    { U = proj₁
    ; R = λ { {X , X-Kan} {Y , Y-Kan} f → PreservesFiller X-Kan Y-Kan f }
    ; Rid = λ _ → refl
    ; _∘R_ = λ _ _ _ → refl
    }
