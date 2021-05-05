{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Posets where

-- The category of partially ordered sets and order-preserving maps.

open import Level
open import Relation.Binary using (Poset; IsEquivalence; _Preserves_⟶_)
open import Relation.Binary.Morphism using (IsOrderHomomorphism)
open import Relation.Binary.Morphism.Bundles using (PosetHomomorphism)
import Relation.Binary.Morphism.Construct.Identity as Id
import Relation.Binary.Morphism.Construct.Composition as Comp

open import Categories.Category

open Poset renaming (_≈_ to ₍_₎_≈_; _≤_ to ₍_₎_≤_)
open PosetHomomorphism using (⟦_⟧; cong)

private
  variable
    a₁ a₂ a₃ b₁ b₂ b₃ : Level
    A B C : Poset a₁ a₂ a₃

module _ {A : Poset a₁ a₂ a₃} {B : Poset b₁ b₂ b₃} where

  infix 4 _≗_

  -- Pointwise equality (on order preserving maps).

  _≗_ : (f g : PosetHomomorphism A B) → Set (a₁ ⊔ b₂)
  f ≗ g = ∀ {x} → ₍ B ₎ ⟦ f ⟧ x ≈ ⟦ g ⟧ x

  ≗-isEquivalence : IsEquivalence _≗_
  ≗-isEquivalence = record
    { refl    = Eq.refl B
    ; sym     = λ f≈g → Eq.sym B f≈g
    ; trans   = λ f≈g g≈h → Eq.trans B f≈g g≈h
    }

  module ≗ = IsEquivalence ≗-isEquivalence

-- The category of posets and order-preserving maps.

Posets : ∀ c ℓ₁ ℓ₂ → Category (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) (c ⊔ ℓ₁ ⊔ ℓ₂) (c ⊔ ℓ₁)
Posets c ℓ₁ ℓ₂ = record
  { Obj       = Poset c ℓ₁ ℓ₂
  ; _⇒_       = PosetHomomorphism
  ; _≈_       = _≗_
  ; id        = λ {A} → Id.posetHomomorphism A
  ; _∘_       = λ f g → Comp.posetHomomorphism g f
  ; assoc     = λ {_ _ _ D} → Eq.refl D
  ; sym-assoc = λ {_ _ _ D} → Eq.refl D
  ; identityˡ = λ {_ B} → Eq.refl B
  ; identityʳ = λ {_ B} → Eq.refl B
  ; identity² = λ {A} → Eq.refl A
  ; equiv     = ≗-isEquivalence
  ; ∘-resp-≈  = λ {_ _ C _ h} f≈h g≈i → Eq.trans C f≈h (cong h g≈i)
  }
