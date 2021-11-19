{-# OPTIONS --without-K --safe #-}

-- A "canonical" presentation of binary coproducts in Setoid.
--
-- Done by analogy with Categories.Category.Instance.Properties.Setoids.Colimits.Canonical

module Categories.Category.Instance.Properties.Setoids.Colimits.Canonical where

open import Level

open import Data.Sum.Relation.Binary.Pointwise using (_⊎ₛ_; inj₁; inj₂)
open import Data.Sum.Function.Setoid

open import Relation.Binary.Bundles using (Setoid)
open import Function.Equality using (cong)
open Setoid using (sym)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Object.Coproduct using (Coproduct)

coproduct : ∀ (o ℓ : Level) → (X Y : Setoid o (o ⊔ ℓ)) → Coproduct (Setoids o (o ⊔ ℓ)) X Y
coproduct _ _ X Y = record
   { A+B = X ⊎ₛ Y
   ; i₁ = inj₁ₛ
   ; i₂ = inj₂ₛ
   ; [_,_] = [_,_]ₛ
   ; inject₁ = λ {_} {f} → cong f
   ; inject₂ = λ {_} {_} {g} → cong g
   ; unique = λ {B} eq₁ eq₂ → λ { (inj₁ x₀≈x₁) → sym B (eq₁ (sym X x₀≈x₁))
                                ; (inj₂ y₀≈y₁) → sym B (eq₂ (sym Y y₀≈y₁))}
   }
