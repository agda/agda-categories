{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Construction.Constant where

open import Level

open import Categories.Category
open import Categories.Category.Instance.One
open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation)
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

const : (d : Category.Obj D) → Functor C D
const {D = D} d = record
  { F₀           = λ _ → d
  ; F₁           = λ _ → id
  ; identity     = refl
  ; homomorphism = sym identity²
  ; F-resp-≈     = λ _ → refl
  }
  where open Category D
        open Equiv

const! : (d : Category.Obj D) → Functor (One {0ℓ} {0ℓ} {0ℓ}) D
const! = const

constˡ : (c : Category.Obj C) → Functor D (Product C D)
constˡ c = const c ※ idF

constʳ : (c : Category.Obj C) → Functor D (Product D C)
constʳ c = idF ※ (const c)

constNat : ∀ {A B} → Category._⇒_ D A B → NaturalTransformation (const {D = D} {C = C} A) (const B)
constNat {D = D} f = record
  { η           = λ _ → f
  ; commute     = λ _ → MR.id-comm D
  ; sym-commute = λ _ → MR.id-comm-sym D
  }
