{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.LawvereTheories where

-- Category of Lawvere Theories

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Functor.Cartesian using (CartesianF)
open import Categories.NaturalTransformation.NaturalIsomorphism
 using (_≃_; associator; sym-associator; unitorˡ; unitorʳ; unitor²; refl; sym; trans; _ⓘₕ_)
open import Categories.Theory.Lawvere using (LawvereTheory; LT-Hom; LT-id; LT-∘)

LawvereTheories : (ℓ e : Level) → Category (suc (ℓ ⊔ e)) (ℓ ⊔ e) (ℓ ⊔ e)
LawvereTheories ℓ e = record
  { Obj = LawvereTheory ℓ e
  ; _⇒_ = LT-Hom
  ; _≈_ = λ H₁ H₂ → cartF.F H₁ ≃ cartF.F H₂
  ; id = LT-id
  ; _∘_ = LT-∘
  ; assoc = λ { {f = f} {g} {h} → associator (cartF.F f) (cartF.F g) (cartF.F h) }
  ; sym-assoc = λ { {f = f} {g} {h} → sym-associator (cartF.F f) (cartF.F g) (cartF.F h) }
  ; identityˡ = unitorˡ
  ; identityʳ = unitorʳ
  ; identity² = unitor²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = _ⓘₕ_
  }
  where open LT-Hom
