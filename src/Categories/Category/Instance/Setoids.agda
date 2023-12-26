{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Setoids where

-- Category of Setoids, aka (Setoid, _⟶_, Setoid ≈)
-- Note the (explicit) levels in each

open import Level using (suc; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Base using (_$_)
import Function.Construct.Composition as Comp
import Function.Construct.Identity as Id
import Function.Construct.Setoid as S

open import Categories.Category.Core using (Category)

open Func
open Setoid

Setoids : ∀ c ℓ → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Setoids c ℓ = record
  { Obj       = Setoid c ℓ
  ; _⇒_       = Func
  ; _≈_       = λ {A} {B} f g → _≈_ (S.function A B) f g
  ; id        = Id.function _
  ; _∘_       = λ f g → Comp.function g f
  ; assoc     = λ {A} {B} {C} {D} {f} {g} {h} x≈y → cong h $ cong g $ cong f x≈y
  ; sym-assoc = λ {A} {B} {C} {D} {f} {g} {h} x≈y → cong h $ cong g $ cong f x≈y
  ; identityˡ = λ {A} {B} {f} x≈y → cong f x≈y
  ; identityʳ = λ {A} {B} {f} x≈y → cong f x≈y
  ; identity² = λ x≈y → x≈y
  ; equiv     = λ {A} {B} → isEquivalence (S.function A B)
  ; ∘-resp-≈  = λ f≈f′ g≈g′ x≈y → f≈f′ (g≈g′ x≈y)
  }
