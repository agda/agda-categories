{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Sets where

-- Category of (Agda) Sets, aka (types, functions, pointwise equality with implicit value)
-- Note the (explicit) levels in each

open import Level
open import Relation.Binary
open import Function using (_∘′_) renaming (id to idf)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

open import Categories.Category

Sets : ∀ o → Category (suc o) o o
Sets o = record
  { Obj       = Set o
  ; _⇒_       = λ c d → c → d
  ; _≈_       = _≗_
  ; id        = idf
  ; _∘_       = _∘′_
  ; assoc     = λ _ → ≡.refl
  ; sym-assoc = λ _ → ≡.refl
  ; identityˡ = λ _ → ≡.refl
  ; identityʳ = λ _ → ≡.refl
  ; identity² = λ _ → ≡.refl
  ; equiv     = record
    { refl  = λ _ → ≡.refl
    ; sym   = λ eq x → ≡.sym (eq x)
    ; trans = λ eq₁ eq₂ x → ≡.trans (eq₁ x) (eq₂ x)
    }
  ; ∘-resp-≈  = resp
  }
  where resp : ∀ {A B C : Set o} {f h : B → C} {g i : A → B} →
                 (f ≗ h) → (g ≗ i) → f ∘′ g ≗ h ∘′ i
        resp {h = h} eq₁ eq₂ x = ≡.trans (eq₁ _) (≡.cong h (eq₂ x))
