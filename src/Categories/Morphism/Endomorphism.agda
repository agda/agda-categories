{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Categories.Morphism.Endomorphism {o ℓ e} (𝒞 : Category o ℓ e) where

open import Algebra.Bundles using (Monoid)
open import Data.Product using (_,_)

open Category 𝒞

End : Obj → Set _
End X = X ⇒ X

End-∘-Monoid : Obj → Monoid _ _
End-∘-Monoid X = record
  { Carrier = End X
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
