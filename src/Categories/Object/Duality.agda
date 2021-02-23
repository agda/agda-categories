{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- Properties relating Initial and Terminal Objects,
-- and Product / Coproduct via op

module Categories.Object.Duality {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Morphism C
open import Categories.Object.Terminal op
open import Categories.Object.Initial C
open import Categories.Object.Product op
open import Categories.Object.Coproduct C

open import Categories.Object.Zero

IsInitial⇒coIsTerminal : ∀ {X} → IsInitial X → IsTerminal X
IsInitial⇒coIsTerminal is⊥ = record
  { !        = !
  ; !-unique = !-unique
  }
  where open IsInitial is⊥

⊥⇒op⊤ : Initial → Terminal
⊥⇒op⊤ i = record
  { ⊤             = ⊥
  ; ⊤-is-terminal = IsInitial⇒coIsTerminal ⊥-is-initial
  }
  where open Initial i

coIsTerminal⇒IsInitial : ∀ {X} → IsTerminal X → IsInitial X
coIsTerminal⇒IsInitial is⊤ = record
  { !        = !
  ; !-unique = !-unique
  }
  where open IsTerminal is⊤

op⊤⇒⊥ : Terminal → Initial
op⊤⇒⊥ t = record
  { ⊥            = ⊤
  ; ⊥-is-initial = coIsTerminal⇒IsInitial ⊤-is-terminal
  }
  where open Terminal t

Coproduct⇒coProduct : ∀ {A B} → Coproduct A B → Product A B
Coproduct⇒coProduct A+B = record
  { A×B      = A+B.A+B
  ; π₁       = A+B.i₁
  ; π₂       = A+B.i₂
  ; ⟨_,_⟩    = A+B.[_,_]
  ; project₁ = A+B.inject₁
  ; project₂ = A+B.inject₂
  ; unique   = A+B.unique
  }
  where
  module A+B = Coproduct A+B

coProduct⇒Coproduct : ∀ {A B} → Product A B → Coproduct A B
coProduct⇒Coproduct A×B = record
  { A+B     = A×B.A×B
  ; i₁      = A×B.π₁
  ; i₂      = A×B.π₂
  ; [_,_]   = A×B.⟨_,_⟩
  ; inject₁ = A×B.project₁
  ; inject₂ = A×B.project₂
  ; unique  = A×B.unique
  }
  where
  module A×B = Product A×B

-- Zero objects are autodual
IsZero⇒coIsZero : ∀ {Z} → IsZero C Z → IsZero op Z
IsZero⇒coIsZero is-zero = record
  { isInitial = record { ! = ! ; !-unique = !-unique }
  ; isTerminal = record { ! = ¡ ; !-unique = ¡-unique }
  }
  where
    open IsZero is-zero

coIsZero⇒IsZero : ∀ {Z} → IsZero op Z → IsZero C Z
coIsZero⇒IsZero co-is-zero = record
  { isInitial = record { ! = ! ; !-unique = !-unique }
  ; isTerminal = record { ! = ¡ ; !-unique = ¡-unique }
  }
  where
    open IsZero co-is-zero

coZero⇒Zero : Zero op → Zero C
coZero⇒Zero zero = record
  { 𝟘 = 𝟘
  ; isZero = coIsZero⇒IsZero isZero
  }
  where
    open Zero zero

Zero⇒coZero : Zero C → Zero op
Zero⇒coZero zero = record
  { 𝟘 = 𝟘
  ; isZero = IsZero⇒coIsZero isZero
  }
  where
    open Zero zero

-- Tests to ensure that dualities are involutive up to definitional equality.
private
  coIsTerminal⟺IsInitial : ∀ {X} (⊥ : IsInitial X) →
    coIsTerminal⇒IsInitial (IsInitial⇒coIsTerminal ⊥) ≡ ⊥
  coIsTerminal⟺IsInitial _ = ≡.refl

  IsInitial⟺coIsTerminal : ∀ {X} (⊤ : IsTerminal X) →
    IsInitial⇒coIsTerminal (coIsTerminal⇒IsInitial ⊤) ≡ ⊤
  IsInitial⟺coIsTerminal _ = ≡.refl

  ⊥⟺op⊤ : (⊤ : Terminal) → ⊥⇒op⊤ (op⊤⇒⊥ ⊤) ≡ ⊤
  ⊥⟺op⊤ _ = ≡.refl

  op⊤⟺⊥ : (⊥ : Initial) → op⊤⇒⊥ (⊥⇒op⊤ ⊥) ≡ ⊥
  op⊤⟺⊥ _ = ≡.refl

  Coproduct⟺coProduct : ∀ {A B} (p : Product A B) → Coproduct⇒coProduct (coProduct⇒Coproduct p) ≡ p
  Coproduct⟺coProduct _ = ≡.refl

  coProduct⟺Coproduct : ∀ {A B} (p : Coproduct A B) → coProduct⇒Coproduct (Coproduct⇒coProduct p) ≡ p
  coProduct⟺Coproduct _ = ≡.refl

  coIsZero⟺IsZero : ∀ {Z} {zero : IsZero op Z} →
    IsZero⇒coIsZero (coIsZero⇒IsZero zero) ≡ zero
  coIsZero⟺IsZero = ≡.refl

  IsZero⟺coIsZero : ∀ {Z} {zero : IsZero C Z} →
    coIsZero⇒IsZero (IsZero⇒coIsZero zero) ≡ zero
  IsZero⟺coIsZero = ≡.refl

  coZero⟺Zero : ∀ {zero : Zero op} →
    Zero⇒coZero (coZero⇒Zero zero) ≡ zero
  coZero⟺Zero = ≡.refl

  Zero⟺coZero : ∀ {zero : Zero C} →
    coZero⇒Zero (Zero⇒coZero zero) ≡ zero
  Zero⟺coZero = ≡.refl
