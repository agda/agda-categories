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
  ; _≈_       = λ {A} {B} f g → _≈_ (S.setoid A B) f g
  ; id        = Id.function _
  ; _∘_       = λ f g → Comp.function g f
  ; assoc     = λ {_} {_} {_} {D} → refl D
  ; sym-assoc = λ {_} {_} {_} {D} → refl D
  ; identityˡ = λ {_} {B} → refl B
  ; identityʳ = λ {_} {B} → refl B
  ; identity² = λ {A} → refl A
  ; equiv     = λ {A} {B} → isEquivalence (S.setoid A B)
  ; ∘-resp-≈  = λ {_} {_} {C} {f} {h} {g} {i} f≈h g≈i {x} → trans C f≈h (cong h g≈i)
  }
