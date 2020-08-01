{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- You can transform functions out of discrete
-- categories into functors.
module Categories.Functor.Construction.FromDiscrete {o ℓ e} (𝒞 : Category o ℓ e) where

open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

open import Categories.Category.Discrete using (Discrete)
open import Categories.Functor.Core using (Functor)

open Category 𝒞
open Equiv

FromDiscrete : ∀ {o} {A : Set o} → (A → Obj) → Functor (Discrete A) 𝒞
FromDiscrete {o} {A = A} select = record
  { F₀ = select
  ; F₁ = λ { ≡.refl → id }
  ; identity = refl
  ; homomorphism = λ { {_} {_} {_} {≡.refl} {≡.refl} → sym identity² }
  ; F-resp-≈ = λ { ≡.refl → refl }
  }
