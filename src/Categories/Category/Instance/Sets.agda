{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Sets where

-- Category of (Agda) Sets, aka (types, functions, pointwise equality with implicit value)
-- Note the (explicit) levels in each

open import Level
open import Relation.Binary
open import Function using (_∘′_) renaming (id to idf)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Category

Sets : ∀ o → Category (suc o) o o
Sets o = record
  { Obj       = Set o
  ; _⇒_       = λ c d → c → d
  ; _≈_       = λ f g → ∀ {x} → f x ≡ g x
  ; id        = idf
  ; _∘_       = _∘′_
  ; assoc     = ≡.refl
  ; sym-assoc = ≡.refl
  ; identityˡ = ≡.refl
  ; identityʳ = ≡.refl
  ; identity² = ≡.refl
  ; equiv     = record
    { refl  = ≡.refl
    ; sym   = λ eq → ≡.sym eq
    ; trans = λ eq₁ eq₂ → ≡.trans eq₁ eq₂
    }
  ; ∘-resp-≈  = resp
  }
  where resp : ∀ {A B C : Set o} {f h : B → C} {g i : A → B} →
                 ({x : B} → f x ≡ h x) →
                 ({x : A} → g x ≡ i x) → {x : A} → f (g x) ≡ h (i x)
        resp {h = h} eq₁ eq₂ = ≡.trans eq₁ (≡.cong h eq₂)
