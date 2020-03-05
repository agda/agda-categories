{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Profunctor where

open import Level

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor.Bifunctor
open import Categories.Functor.Hom

Profunctor : ∀ {o ℓ e} {o′ ℓ′ e′} → Category o ℓ e → Category o′ ℓ′ e′ → Set _
Profunctor {ℓ = ℓ} {e} {ℓ′ = ℓ′} {e′} C D = Bifunctor (Category.op D) C (Setoids (ℓ ⊔ ℓ′) (e ⊔ e′))

id : ∀ {o ℓ e} → {C : Category o ℓ e} → Profunctor C C
id {C = C} = Hom[ C ][-,-]
