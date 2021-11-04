{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Profunctor where

open import Level

open import Data.Product
open import Relation.Binary.Bundles
open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Hom

Profunctor : ∀ {o ℓ e} {o′ ℓ′ e′} → Category o ℓ e → Category o′ ℓ′ e′ → Set _
Profunctor {ℓ = ℓ} {e} {ℓ′ = ℓ′} {e′} C D = Bifunctor (Category.op D) C (Setoids (ℓ ⊔ ℓ′) (e ⊔ e′))

id : ∀ {o ℓ e} → {C : Category o ℓ e} → Profunctor C C
id {C = C} = Hom[ C ][-,-]

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′

-- stub for representable profunctors
repˡ : (F : Functor C D) → Profunctor D C
repˡ F = record
  { F₀ = {!   !}
  ; F₁ = {!   !}
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  }
  where
  F0 : Σ (Category.Obj C) (λ x → Category.Obj D) → Setoid (ℓ ⊔ ℓ′) (e ⊔ e′)
  F0 (c , d) = record
    { Carrier = {!   !}
    ; _≈_ = {! _≈_   !}
    ; isEquivalence = record { refl = {!   !} ; sym = {!   !} ; trans = {!   !} }
    }

repʳ : (F : Functor C D) → Profunctor C D
repʳ F = record
  { F₀ = λ x → {!   !}
  ; F₁ = {!   !}
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  }
