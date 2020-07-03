{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.LawvereTheories where

-- Category of Lawvere Theories

open import Level

open import Categories.Category
open import Categories.Functor.Cartesian.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Theory.Lawvere

LawvereTheories : (o ℓ e : Level) → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
LawvereTheories o ℓ e = record
  { Obj = FiniteProduct o ℓ e
  ; _⇒_ = LT-Hom
  ; _≈_ = λ H₁ H₂ → F H₁ ≃ F H₂
  ; id = LT-id
  ; _∘_ = LT-∘
  ; assoc = λ { {f = f} {g} {h} → associator (F f) (F g) (F h)}
  ; sym-assoc = λ { {f = f} {g} {h} → sym-associator (F f) (F g) (F h)}
  ; identityˡ = unitorˡ
  ; identityʳ = unitorʳ
  ; identity² = unitor²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = _ⓘₕ_
  }
  where open LT-Hom
