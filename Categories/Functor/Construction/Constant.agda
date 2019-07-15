{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Construction.Constant where

open import Level

open import Categories.Category
open import Categories.Functor hiding (id)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

Constant : {D : Category o′ ℓ′ e′} {C : Category o ℓ e} (x : Category.Obj D) → Functor C D
Constant {D = D} x = record
  { F₀ = λ _ → x
  ; F₁ = λ _ → id
  ; identity = refl
  ; homomorphism = sym identityˡ
  ; F-resp-≈ = λ _ → refl
  }
  where open Category D; open Equiv
