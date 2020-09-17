{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Posets where

-- The category of partially ordered sets and order-preserving maps.

open import Level
open import Relation.Binary using (Poset; IsEquivalence; _Preserves_⟶_)
open import Relation.Binary.OrderMorphism using (_⇒-Poset_; id; _∘_)

open import Categories.Category

open Poset renaming (_≈_ to ₍_₎_≈_; _≤_ to ₍_₎_≤_)
open _⇒-Poset_

module _ {a₁ a₂ a₃ b₁ b₂ b₃} {A : Poset a₁ a₂ a₃} {B : Poset b₁ b₂ b₃} where

  infix 4 _≗_

  -- Order morphisms preserve equality.

  fun-resp-≈ : (f : A ⇒-Poset B) → fun f Preserves ₍ A ₎_≈_ ⟶ ₍ B ₎_≈_
  fun-resp-≈ f x≈y = antisym B (monotone f (reflexive A x≈y))
                               (monotone f (reflexive A (Eq.sym A x≈y)))

  -- Pointwise equality (on order preserving maps).

  _≗_ : (f g : A ⇒-Poset B) → Set (a₁ ⊔ b₂)
  f ≗ g = ∀ {x} → ₍ B ₎ fun f x ≈ fun g x

  ≗-isEquivalence : IsEquivalence _≗_
  ≗-isEquivalence = record
    { refl    = Eq.refl B
    ; sym     = λ f≈g → Eq.sym B f≈g
    ; trans   = λ f≈g g≈h → Eq.trans B f≈g g≈h
    }

  module ≗ = IsEquivalence ≗-isEquivalence

-- The category of posets and order-preserving maps.

Posets : ∀ c ℓ₁ ℓ₂ → Category (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) (c ⊔ ℓ₂) (c ⊔ ℓ₁)
Posets c ℓ₁ ℓ₂ = record
  { Obj       = Poset c ℓ₁ ℓ₂
  ; _⇒_       = _⇒-Poset_
  ; _≈_       = _≗_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = λ {_ _ _ D} → Eq.refl D
  ; sym-assoc = λ {_ _ _ D} → Eq.refl D
  ; identityˡ = λ {_ B} → Eq.refl B
  ; identityʳ = λ {_ B} → Eq.refl B
  ; identity² = λ {A} → Eq.refl A
  ; equiv     = ≗-isEquivalence
  ; ∘-resp-≈  = λ {_ _ C _ h} f≈h g≈i → Eq.trans C f≈h (fun-resp-≈ h g≈i)
  }

