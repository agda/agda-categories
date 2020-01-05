{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Construction.Zero where

-- The Zero functor maps everything to the initial object of a
-- category (when it exists). Note quite const.

open import Level

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Object.Initial

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

Zero : Initial D → Functor C D
Zero {D = D} init = record
  { F₀ = λ _ → ⊥
  ; F₁ = λ _ → id
  ; identity = Equiv.refl
  ; homomorphism = Equiv.sym identity²
  ; F-resp-≈ = λ _ → Equiv.refl
  }
  where
  open Initial init
  open Category D
