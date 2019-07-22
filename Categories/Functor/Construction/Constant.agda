{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Construction.Constant where

open import Level

open import Categories.Category
open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation)

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

const : Category.Obj D → Functor C D
const {D = D} A = record
  { F₀           = λ _ → A
  ; F₁           = λ _ → id
  ; identity     = refl
  ; homomorphism = sym identityˡ
  ; F-resp-≈     = λ _ → refl
  }
  where open Category D
        open Equiv

constˡ : Category.Obj C → Functor D (Product C D)
constˡ A = const A ※ idF

constʳ : Category.Obj C → Functor D (Product D C)
constʳ A = idF ※ (const A)

constNat : ∀ {A B} → Category._⇒_ D A B → NaturalTransformation (const {D = D} {C = C} A) (const B)
constNat {D = D} f = record
  { η       = λ _ → f
  ; commute = λ _ → id-comm
  }
  where open Category D
