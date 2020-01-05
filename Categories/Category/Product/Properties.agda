{-# OPTIONS --without-K --safe #-}
module Categories.Category.Product.Properties where

-- properties of the product _※_ of Functors (so probably should be renamed?)

open import Level
open import Data.Product

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper) renaming (id to idNI)
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Category.Product
open import Categories.Morphism
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

-- variables don't work quite right, use anonymous module instead
module _ {A : Category o ℓ e} {B : Category o′ ℓ′ e′} {C : Category o″ ℓ″ e″}
         {i : Functor C A} {j : Functor C B} where

  project₁ : πˡ ∘F (i ※ j) ≃ i
  project₁ = record
    { F⇒G = ntHelper record { η = λ _ → id ; commute = λ _ → id-comm-sym }
    ; F⇐G = ntHelper record { η = λ _ → id ; commute = λ _ → id-comm-sym }
    ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityʳ }
    }
    where open Category A; open MR.Basic A

  project₂ : πʳ ∘F (i ※ j) ≃ j
  project₂ = record
    { F⇒G = ntHelper record { η = λ _ → id ; commute = λ _ → id-comm-sym }
    ; F⇐G = ntHelper record { η = λ _ → id ; commute = λ _ → id-comm-sym }
    ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityʳ }
    }
    where open Category B; open MR.Basic B

  unique : {h : Functor C (Product A B)} →
        πˡ ∘F h ≃ i → πʳ ∘F h ≃ j → (i ※ j) ≃ h
  unique πˡ→i πʳ→j = record
    { F⇒G = ntHelper record
      { η       = < L⇐.η , R⇐.η >
      ; commute = < L⇐.commute , R⇐.commute >
      }
    ; F⇐G = ntHelper record
      { η       = < L⇒.η , R⇒.η >
      ; commute = < L⇒.commute , R⇒.commute >
      }
    ; iso = λ X → let L = iso πˡ→i X
                      R = iso πʳ→j X in record
      { isoˡ = isoʳ L , isoʳ R
      ; isoʳ = isoˡ L , isoˡ R
      }
    }
    where
      open NaturalIsomorphism
      module L⇐ = NaturalTransformation (F⇐G πˡ→i)
      module R⇐ = NaturalTransformation (F⇐G πʳ→j)
      module L⇒ = NaturalTransformation (F⇒G πˡ→i)
      module R⇒ = NaturalTransformation (F⇒G πʳ→j)
      open Iso

-- further properties of products
module _ (C : Category o ℓ e) (D : Category o′ ℓ′ e′) where

  private
    C×D : Category _ _ _
    C×D = Product C D
    module C×D = Category C×D
    module C = Category C
    module D = Category D

  -- TODO: write an "essentially-equal" combinator for cases such as these?
  πˡ※πʳ≃id : (πˡ ※ πʳ) ≃ idF {C = C×D}
  πˡ※πʳ≃id = record
    { F⇒G = ntHelper record { η = λ _ → C×D.id ; commute = λ _ → MR.id-comm-sym C , MR.id-comm-sym D }
    ; F⇐G = ntHelper record { η = λ _ → C×D.id ; commute = λ _ → MR.id-comm-sym C , MR.id-comm-sym D }
    ; iso = λ X → record
      { isoˡ = C.identityˡ , D.identityˡ
      ; isoʳ = C.identityʳ , D.identityʳ
      }
    }

  ※-distrib : {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ : Level} {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂}
    → (F : Functor B C) → (G : Functor B D) → (H : Functor A B)
    → ((F ∘F H) ※ (G ∘F H)) ≃ ((F ※ G) ∘F H)
  ※-distrib F G H = record
    { F⇒G = ntHelper record { η = λ _ → C×D.id ; commute = λ _ → MR.id-comm-sym C , MR.id-comm-sym D }
    ; F⇐G = ntHelper record { η = λ _ → C×D.id ; commute = λ _ → MR.id-comm-sym C , MR.id-comm-sym D }
    ; iso = λ X → record
      { isoˡ = C.identityˡ , D.identityˡ
      ; isoʳ = C.identityʳ , D.identityʳ
      }
    }

  ※-distrib₂ : {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ : Level} {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂}
    → (F : Functor B C) → (G : Functor B D)
    → ((F ∘F πˡ) ※ (G ∘F πʳ)) ≃ (F ⁂ G)
  ※-distrib₂ F G = record
    { F⇒G = ntHelper record { η = λ X → C.id , D.id ; commute = λ _ → MR.id-comm-sym C , MR.id-comm-sym D }
    ; F⇐G = ntHelper record { η = λ X → C.id , D.id ; commute = λ _ → MR.id-comm-sym C , MR.id-comm-sym D }
    ; iso = λ X → record { isoˡ = C.identityˡ , D.identityʳ  ; isoʳ = C.identityʳ , D.identityʳ }
    }
