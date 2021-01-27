{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Posets where

-- The category of partially ordered sets and order-preserving maps.

open import Level
open import Relation.Binary using (Poset; IsEquivalence; _Preserves_⟶_)
open import Relation.Binary.Morphism using (IsOrderHomomorphism)
import Relation.Binary.Morphism.Construct.Identity as Id
import Relation.Binary.Morphism.Construct.Composition as Comp

open import Categories.Category

open Poset renaming (_≈_ to ₍_₎_≈_; _≤_ to ₍_₎_≤_)

private
  variable
    a₁ a₂ a₃ b₁ b₂ b₃ : Level

record _⇒-Poset_ (A : Poset a₁ a₂ a₃) (B : Poset b₁ b₂ b₃) : Set (a₁ ⊔ a₂ ⊔ a₃ ⊔ b₁ ⊔ b₂ ⊔ b₃)  where
  field
    fun : Carrier A → Carrier B
    isOrderHomomorphism : IsOrderHomomorphism ₍ A ₎_≈_ ₍ B ₎_≈_ ₍ A ₎_≤_ ₍ B ₎_≤_ fun

  open IsOrderHomomorphism isOrderHomomorphism public
    renaming (mono to monotone)

open _⇒-Poset_

⇒-Poset-id : ∀ {A : Poset a₁ a₂ a₃} → A ⇒-Poset A
⇒-Poset-id = record
  { isOrderHomomorphism = Id.isOrderHomomorphism _ _
  }

⇒-Poset-∘ : ∀ {A B C : Poset a₁ a₂ a₃} → B ⇒-Poset C → A ⇒-Poset B → A ⇒-Poset C
⇒-Poset-∘ B⇒C A⇒B = record
  { isOrderHomomorphism = Comp.isOrderHomomorphism (isOrderHomomorphism A⇒B) (isOrderHomomorphism B⇒C)
  }

module _ {A : Poset a₁ a₂ a₃} {B : Poset b₁ b₂ b₃} where

  infix 4 _≗_

  -- Order morphisms preserve equality.
  mono⇒cong : ∀ {f} → f Preserves ₍ A ₎_≤_ ⟶ ₍ B ₎_≤_ → f Preserves ₍ A ₎_≈_ ⟶ ₍ B ₎_≈_
  mono⇒cong {f} monotone x≈y = antisym B
    (monotone (reflexive A x≈y))
    (monotone (reflexive A (Eq.sym A x≈y)))
                               
  ⇒-Poset-helper : ∀ f → f Preserves ₍ A ₎_≤_ ⟶ ₍ B ₎_≤_ → A ⇒-Poset B
  ⇒-Poset-helper f mono = record
    { isOrderHomomorphism = record
      { cong = mono⇒cong mono
      ; mono = mono
      }
    }

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

Posets : ∀ c ℓ₁ ℓ₂ → Category (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) (c ⊔ ℓ₁ ⊔ ℓ₂) (c ⊔ ℓ₁)
Posets c ℓ₁ ℓ₂ = record
  { Obj       = Poset c ℓ₁ ℓ₂
  ; _⇒_       = _⇒-Poset_
  ; _≈_       = _≗_
  ; id        = ⇒-Poset-id
  ; _∘_       = ⇒-Poset-∘
  ; assoc     = λ {_ _ _ D} → Eq.refl D
  ; sym-assoc = λ {_ _ _ D} → Eq.refl D
  ; identityˡ = λ {_ B} → Eq.refl B
  ; identityʳ = λ {_ B} → Eq.refl B
  ; identity² = λ {A} → Eq.refl A
  ; equiv     = ≗-isEquivalence
  ; ∘-resp-≈  = λ {_ _ C _ h} f≈h g≈i → Eq.trans C f≈h (cong h g≈i)
  }
