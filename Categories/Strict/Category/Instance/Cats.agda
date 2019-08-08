{-# OPTIONS --without-K --safe #-}
module Categories.Strict.Category.Instance.Cats where

-- The (large) weak category of (small) strict categories.
-- It cannot be a strict category itself, as ≡ isn't dependent enough (without K)

open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Categories.Strict.Category using (Category)
open import Categories.Strict.Functor

open import Categories.Category renaming (Category to WeakCategory)

private
  variable
    o ℓ : Level
    C D E : Category o ℓ

Cats : ∀ o ℓ → WeakCategory (suc (o ⊔ ℓ)) (o ⊔ ℓ) (o ⊔ ℓ)
Cats o ℓ = record
  { Obj       = Category o ℓ
  ; _⇒_       = Functor
  ; id        = id
  ; _≈_       = _≡F_
  ; _∘_       = _∘F_
  ; assoc     = λ _ → refl , refl
  ; identityˡ = λ _ → refl , refl
  ; identityʳ = λ _ → refl , refl
  ; equiv     = ≡F-equiv
  ; ∘-resp-≈ = λ {A} {B} {C} {f} {h} {g} {i} x y → ∘F-perserves-≡F {A = A} {B} {C} {f} {h} {g} {i} x y
  }
  where open Functor
