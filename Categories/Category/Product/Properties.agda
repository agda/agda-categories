{-# OPTIONS --without-K --safe #-}
module Categories.Category.Product.Properties where

open import Level
open import Data.Product

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Category.Product
open import Categories.Morphism

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

project₁ : {A : Category o ℓ e} {B : Category o′ ℓ′ e′} {C : Category o″ ℓ″ e″}
  {h : Functor C A} {i : Functor C B} → NaturalIsomorphism (πˡ ∘F (h ※ i)) h
project₁ {A = A} = record
  { F⇒G = record { η = λ _ → id ; commute = λ _ → ⟺ id-comm }
  ; F⇐G = record { η = λ _ → id ; commute = λ _ → ⟺ id-comm }
  ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityʳ }
  }
  where open Category A; open HomReasoning

project₂ : {A : Category o ℓ e} {B : Category o′ ℓ′ e′} {C : Category o″ ℓ″ e″}
  {h : Functor C A} {i : Functor C B} → NaturalIsomorphism (πʳ ∘F (h ※ i)) i
project₂ {B = B} = record
  { F⇒G = record { η = λ _ → id ; commute = λ _ → ⟺ id-comm }
  ; F⇐G = record { η = λ _ → id ; commute = λ _ → ⟺ id-comm }
  ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityʳ }
  }
  where open Category B; open HomReasoning

unique : {A : Category o ℓ e} {B : Category o′ ℓ′ e′} {C : Category o″ ℓ″ e″}
      {h : Functor C (Product A B)} {i : Functor C A} {j : Functor C B} →
      NaturalIsomorphism (πˡ ∘F h) i →
      NaturalIsomorphism (πʳ ∘F h) j → NaturalIsomorphism (i ※ j) h
unique πˡ→i πʳ→j = record
  { F⇒G = record
    { η       = < L⇐.η , R⇐.η >
    ; commute = < L⇐.commute , R⇐.commute >
    }
  ; F⇐G = record
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
