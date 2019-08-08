{-# OPTIONS --without-K --safe #-}

module Categories.Strict.2-Category.Instance.Cats where


open import Level

open import Categories.Strict.2-Category
open import Categories.Strict.Category
-- open import Categories.Strict.Category.Construction.Functors using (Functors)

Cats-is-a : (o ℓ : Level) → 2-Category o ℓ (suc (o ⊔ ℓ))
Cats-is-a o ℓ = record
  { Obj = Category o ℓ
  ; hom = {!Functor!}
  ; id = {!!}
  ; ⊚ = {!!}
  ; ⊚-assoc = {!!}
  ; unitˡ = {!!}
  ; unitʳ = {!!}
  }
