{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Instance.Simplex where

open import Level
open import Data.Product
open import Data.Fin.Base using (Fin; _≤_)
open import Data.Nat.Base using (ℕ)
open import Function renaming (id to idF; _∘_ to _∙_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

Δ : Category 0ℓ 0ℓ 0ℓ
Δ = record
  { Obj       = ℕ
  ; _⇒_       = λ m n → Σ (Fin m → Fin n) (λ f → _≤_ =[ f ]⇒ _≤_)
  ; _≈_       = λ { (f , mf) (g , mg) → ∀ x → f x ≡ g x }
  ; id        = idF , idF
  ; _∘_       = λ { (f , mf) (g , mg) → f ∙ g , mf ∙ mg }
  ; assoc     = λ _ → refl
  ; sym-assoc = λ _ → refl
  ; identityˡ = λ _ → refl
  ; identityʳ = λ _ → refl
  ; identity² = λ _ → refl
  ; equiv     = record
    { refl  = λ _ → refl
    ; sym   = λ eq x → sym (eq x)
    ; trans = λ eq₁ eq₂ x → trans (eq₁ x) (eq₂ x)
    }
  ; ∘-resp-≈  = λ {_ _ _ f g h i} eq₁ eq₂ x → trans (cong (λ t → proj₁ f t) (eq₂ x)) (eq₁ (proj₁ i x))
  }
