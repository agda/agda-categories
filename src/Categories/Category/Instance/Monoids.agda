{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Monoids where

-- The category of Monoids and Homomorphisms.
-- The category of Commutative Monoids and Homomorphisms as well.

open import Level
open import Algebra
open import Algebra.Morphism
open import Data.Product using (Σ; proj₁; proj₂; _,_)
open import Function.Base hiding (_∘_) renaming (id to id→; _∘′_ to _⊚_)

open import Categories.Category

private
  variable
    c ℓ : Level
  open Monoid hiding (_≈_)
  open IsMonoidMorphism

  id′ : {A : Monoid c ℓ} → Σ (Carrier A → Carrier A) (IsMonoidMorphism A A)
  id′ {A = A} = id→ , (record
    { sm-homo = record
      { ⟦⟧-cong = id→
      ; ∙-homo = λ _ _ → Monoid.refl A
      }
    ; ε-homo = Monoid.refl A
    })
  _∘′_ : {A B C : Monoid c ℓ} →
      Σ (Carrier B → Carrier C) (IsMonoidMorphism B C) →
      Σ (Carrier A → Carrier B) (IsMonoidMorphism A B) →
      Σ (Carrier A → Carrier C) (IsMonoidMorphism A C)
  _∘′_ {C = C} (f , mf) (g , mg) = f ⊚ g  , record
    { sm-homo = record
      { ⟦⟧-cong = ⟦⟧-cong mf ⊚ ⟦⟧-cong mg
      ; ∙-homo = λ x y → Monoid.trans C (⟦⟧-cong mf (∙-homo mg x y)) (∙-homo mf (g x) (g y))
      }
    ; ε-homo = Monoid.trans C (⟦⟧-cong mf (ε-homo mg)) (ε-homo mf)
    }

Monoids : (c ℓ : Level) → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Monoids c ℓ = record
  { Obj = Monoid c ℓ
  ; _⇒_ = λ m₁ m₂ → Σ (Carrier m₁ → Carrier m₂) (IsMonoidMorphism m₁ m₂)
  ; _≈_ = λ {_} {m} H₁ H₂ → let open Monoid m in ∀ x → proj₁ H₁ x ≈ proj₁ H₂ x
  ; id = id′
  ; _∘_ = _∘′_
  ; assoc = λ {_} {_} {_} {D} _ → Monoid.refl D
  ; sym-assoc = λ {_} {_} {_} {D} _ → Monoid.refl D
  ; identityˡ = λ {_} {B} _ → Monoid.refl B
  ; identityʳ = λ {_} {B} _ → Monoid.refl B
  ; identity² = λ {A} _ → Monoid.refl A
  ; equiv = λ {A} {B} → record
    { refl = λ _ → Monoid.refl B
    ; sym = λ s x → Monoid.sym B (s x)
    ; trans = λ i≈j j≈k a → Monoid.trans B (i≈j a) (j≈k a)
    }
  ; ∘-resp-≈ = λ {_} {_} {C} {f} f≈h g≈i a → Monoid.trans C (⟦⟧-cong (proj₂ f) (g≈i a)) (f≈h _)
  }

CommMonoids : (c ℓ : Level) → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
CommMonoids c ℓ = record
  { Obj = CommutativeMonoid c ℓ
  ; _⇒_ = λ m₁ m₂ → Σ (Carrier m₁ → Carrier m₂) (IsCommutativeMonoidMorphism m₁ m₂)
  ; _≈_ = λ {_} {m} H₁ H₂ → let open CommutativeMonoid m in ∀ x → proj₁ H₁ x ≈ proj₁ H₂ x
  ; id = id→ , record { mn-homo = proj₂ id′ }
  ; _∘_ = λ {A} {B} {C} m₁ m₂ →
    proj₁ m₁ ⊚ proj₁ m₂ ,
    record { mn-homo = proj₂ ((proj₁ m₁ , mn-homo (proj₂ m₁)) ∘′ (proj₁ m₂ , mn-homo (proj₂ m₂))) }
  ; assoc = λ {_} {_} {_} {D} _ → refl D
  ; sym-assoc = λ {_} {_} {_} {D} _ → refl D
  ; identityˡ = λ {_} {B} _ → refl B
  ; identityʳ = λ {_} {B} _ → refl B
  ; identity² = λ {A} _ → refl A
  ; equiv = λ {A} {B} → record
    { refl = λ _ → refl B
    ; sym = λ s x → sym B (s x)
    ; trans = λ i≈j j≈k a → trans B (i≈j a) (j≈k a)
    }
  ; ∘-resp-≈ = λ {_} {_} {C} {f} f≈h g≈i a → trans C (⟦⟧-cong (proj₂ f) (g≈i a)) (f≈h _)
  }
  where
  open CommutativeMonoid hiding (_≈_)
  open IsCommutativeMonoidMorphism
