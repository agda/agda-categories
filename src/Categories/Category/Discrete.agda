{-# OPTIONS --without-K --safe #-}
module Categories.Category.Discrete where

open import Level
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality as ≡

open import Categories.Category
open import Categories.Functor

Discrete : ∀ {a} (A : Set a) → Category a a a
Discrete A = record
  { Obj       = A
  ; _⇒_       = _≡_
  ; _≈_       = _≡_
  ; id        = refl
  ; _∘_       = flip ≡.trans
  ; assoc     = λ {_ _ _ _ g} → sym (trans-assoc g)
  ; sym-assoc = λ {_ _ _ _ g} → trans-assoc g
  ; identityˡ = λ {_ _ f} → trans-reflʳ f
  ; identityʳ = refl
  ; identity² = refl
  ; equiv     = isEquivalence
  ; ∘-resp-≈  = λ where
    refl refl → refl
  }

module _ {a o ℓ e} {A : Set a} (C : Category o ℓ e) where
  open Category C renaming (id to one)

  module _ (f : A → Obj) where

    lift-func : Functor (Discrete A) C
    lift-func = record
      { F₀           = f
      ; F₁           = λ { refl → one }
      ; identity     = Equiv.refl
      ; homomorphism = λ { {_} {_} {_} {refl} {refl} → Equiv.sym identity² }
      ; F-resp-≈     = λ { {_} {_} {refl} refl → Equiv.refl }
      }
