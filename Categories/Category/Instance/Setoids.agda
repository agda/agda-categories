{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Setoids where

-- Category of Setoids, aka (Setoid, _⟶_, Setoid ≈)
-- Note the (explicit) levels in each

open import Level
open import Relation.Binary
open import Function.Equality as SΠ renaming (id to ⟶-id)

open import Categories.Category

Setoids : ∀ c ℓ → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Setoids c ℓ = record
  { Obj       = Setoid c ℓ
  ; _⇒_       = _⟶_
  ; _≈_       = λ {A B} → Setoid._≈_ (A ⇨ B)
  ; id        = ⟶-id
  ; _∘_       = _∘_
  ; assoc     = λ {_ _ _ D} {f g h} → cong (h ∘ g ∘ f)
  ; sym-assoc = λ {_ _ _ D} {f g h} → cong (h ∘ g ∘ f)
  ; identityˡ = λ {_ _} {f} → cong f
  ; identityʳ = λ {_ _} {f} → cong f
  ; identity² = λ eq → eq
  ; equiv     = λ {A B} → Setoid.isEquivalence (A ⇨ B)
  ; ∘-resp-≈  = λ f≡h g≡i x≡y → f≡h (g≡i x≡y)
  }
