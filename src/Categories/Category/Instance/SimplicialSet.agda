{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.SimplicialSet where

open import Level

open import Categories.Category
open import Categories.Category.Instance.Simplex
open import Categories.Category.Construction.Presheaves

SimplicialSet : ∀ o ℓ → Category (suc (o ⊔ ℓ)) (o ⊔ ℓ) (o ⊔ ℓ)
SimplicialSet o ℓ = Presheaves {o′ = o} {ℓ′ = ℓ} Δ
