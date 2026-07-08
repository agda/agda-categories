{-# OPTIONS --without-K --safe #-}

-- The endomorphisms of an object form a monoid under composition.
-- See https://ncatlab.org/nlab/show/endomorphism+monoid for this.

open import Categories.Category.Core using (Category)

module Categories.Object.Endomorphism {o ℓ e} (𝒞 : Category o ℓ e) where

open import Algebra.Bundles using (Monoid)
open import Data.Product using (_,_)

open Category 𝒞

Endo : Obj → Set _
Endo X = X ⇒ X

Endo-∘-Monoid : Obj → Monoid _ _
Endo-∘-Monoid X = record
  { Carrier = Endo X
  ; _≈_ = _≈_
  ; _∙_ = _∘_
  ; ε = id
  ; isMonoid = record
    { isSemigroup = record
      { assoc = λ _ _ _ → assoc
      ; isMagma = record
        { isEquivalence = equiv
        ; ∙-cong = ∘-resp-≈
        }
      }
    ; identity = (λ _ → identityˡ) , (λ _ → identityʳ)
    }
  }
