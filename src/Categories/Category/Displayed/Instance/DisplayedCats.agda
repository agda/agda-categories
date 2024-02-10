{-# OPTIONS --safe --without-K #-}

module Categories.Category.Displayed.Instance.DisplayedCats where

open import Level

open import Categories.Category
open import Categories.Category.Displayed
open import Categories.Category.Instance.Cats
open import Categories.Functor.Displayed
open import Categories.NaturalTransformation.NaturalIsomorphism.Displayed

DisplayedCats : ∀ o ℓ e o′ ℓ′ e′ → Displayed (Cats o ℓ e) (o ⊔ ℓ ⊔ e ⊔ suc (o′ ⊔ ℓ′ ⊔ e′)) (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′)
DisplayedCats o ℓ e o′ ℓ′ e′ = record
  { Obj[_] = λ B → Displayed B o′ ℓ′ e′
  ; _⇒[_]_ = λ C F D → DisplayedFunctor C D F
  ; _≈[_]_ = λ F′ F≃G G′ → DisplayedNaturalIsomorphism F′ G′ F≃G
  ; id′ = id′
  ; _∘′_ = _∘F′_
  ; identityˡ′ = unitorˡ′
  ; identityʳ′ = unitorʳ′
  ; identity²′ = unitor²′
  ; assoc′ = λ {_ _ _ _ _ _ _ _ _ _ _ F′ G′ H′} → associator′ H′ G′ F′
  ; sym-assoc′ = λ {_ _ _ _ _ _ _ _ _ _ _ F′ G′ H′} → sym-associator′ H′ G′ F′
  ; equiv′ = isDisplayedEquivalence
  ; ∘′-resp-≈[] = _ⓘₕ′_
  }
