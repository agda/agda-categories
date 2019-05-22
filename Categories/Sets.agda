{-# OPTIONS --without-K --safe #-}
module Categories.Sets where

open import Level
open import Relation.Binary
open import Function.Equality as SΠ renaming (id to ⟶-id)
open import Function using (_∘′_) renaming (id to identity)

open import Categories.Category

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

private
  variable
    o ℓ e : Level

Sets : ∀ o → Category _ _ _
Sets o = record
  { Obj       = Set o
  ; _⇒_       = λ d c → d → c
  ; _≈_       = λ f g → ∀ {x} → f x ≡ g x
  ; id        = identity
  ; _∘_       = _∘′_
  ; assoc     = ≡.refl
  ; identityˡ = ≡.refl
  ; identityʳ = ≡.refl
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
        resp {i = i} eq₁ eq₂ {x}
          rewrite eq₂ {x} | eq₁ {i x} = ≡.refl

Setoids : ∀ c ℓ → Category _ _ _
Setoids c ℓ = record
  { Obj       = Setoid c ℓ
  ; _⇒_       = _⟶_
  ; _≈_       = λ {A B} → Setoid._≈_ (A ⇨ B)
  ; id        = ⟶-id
  ; _∘_       = _∘_
  ; assoc     = λ {_ _ _ D} {f g h} → cong (h ∘ g ∘ f)
  ; identityˡ = λ {_ _} {f} → cong f
  ; identityʳ = λ {_ _} {f} → cong f
  ; equiv     = λ {A B} → Setoid.isEquivalence (A ⇨ B)
  ; ∘-resp-≈  = λ f≡h g≡i x≡y → f≡h (g≡i x≡y)
  }
