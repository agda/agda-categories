{-# OPTIONS --without-K --safe #-}
module Categories.Functor.DistributiveLaw where

open import Level
open import Categories.Category using (Category)
open import Categories.Functor using (Endofunctor; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)

private
  variable
    o ℓ e : Level

DistributiveLaw : {C : Category o ℓ e} → (T F : Endofunctor C) → Set (o ⊔ ℓ ⊔ e)
DistributiveLaw {C = C} T F = NaturalTransformation (T ∘F F) (F ∘F T) where open Category C
