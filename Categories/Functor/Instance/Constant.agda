{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Instance.Constant where

open import Level

open import Categories.Category
open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

const : Category.Obj C → Functor D C
const {C = C} c = record
  { F₀           = λ _ → c
  ; F₁           = λ _ → Category.id C
  ; identity     = refl
  ; homomorphism = sym identityˡ
  ; F-resp-≈     = λ _ → refl
  }
  where open Category C
        open HomReasoning

constˡ : Category.Obj C → Functor D (Product C D)
constˡ c = const c ※ idF

constʳ : Category.Obj C → Functor D (Product D C)
constʳ c = idF ※ (const c)
