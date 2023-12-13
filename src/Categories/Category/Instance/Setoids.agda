{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Setoids where

-- Category of Setoids, aka (Setoid, _⟶_, Setoid ≈)
-- Note the (explicit) levels in each

open import Level
open import Relation.Binary
open import Function.Bundles
import Function.Construct.Composition as Comp
import Function.Construct.Identity as Id

open import Categories.Category

Setoids : ∀ c ℓ → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Setoids c ℓ = record
  { Obj       = Setoid c ℓ
  ; _⇒_       = Func
  ; _≈_       = λ {A B} → λ f g → ∀ {x y} → Setoid._≈_ A x y → Setoid._≈_ B (f ⟨$⟩ x) (g ⟨$⟩ y)
  ; id        = Id.function _
  ; _∘_       = λ f g → Comp.function g f
  ; assoc     = λ {A} {B} {C} {D} {f} {g} {h} x≈y → Func.cong h (Func.cong g (Func.cong f x≈y))
  ; sym-assoc = λ {A} {B} {C} {D} {f} {g} {h} x≈y → Func.cong h (Func.cong g (Func.cong f x≈y))
  ; identityˡ = λ {A} {B} {f} x≈y → Func.cong f x≈y
  ; identityʳ = λ {A} {B} {f} x≈y → Func.cong f x≈y
  ; identity² = λ x≈y → x≈y
  ; equiv     = λ {A} {B} → record
    { refl  = λ {f} x≈y → Func.cong f x≈y
    ; sym   = λ f≈g x≈y → Setoid.sym B (f≈g (Setoid.sym A x≈y))
    ; trans = λ f≈g g≈h x≈y → Setoid.trans B (f≈g x≈y) (g≈h (Setoid.refl A))
    }
  ; ∘-resp-≈  = λ f≈f′ g≈g′ x≈y → f≈f′ (g≈g′ x≈y)
  }
