{-# OPTIONS --without-K --safe #-}

module Categories.Category.Finite.Fin.Construction.Discrete where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin; suc)
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_ ; refl)

open import Categories.Category.Finite.Fin
open import Categories.Category.Core using (Category)

private
  card : ∀ {n} (j k : Fin n) → ℕ
  card {ℕ.suc n} 0F 0F           = 1
  card {ℕ.suc n} 0F (suc k)      = 0
  card {ℕ.suc n} (suc j) 0F      = 0
  card {ℕ.suc n} (suc j) (suc k) = card j k

  id : ∀ {n} (a : Fin n) → Fin (card a a)
  id {ℕ.suc n} 0F      = 0F
  id {ℕ.suc n} (suc a) = id a

  comp : ∀ n {a b c : Fin n} → Fin (card b c) → Fin (card a b) → Fin (card a c)
  comp (ℕ.suc n) {0F} {0F} {0F} f g = 0F
  comp (ℕ.suc n) {suc a} {suc b} {suc c} f g = comp n f g

  assoc : ∀ n {a b c d : Fin n}
            {f : Fin (card a b)} {g : Fin (card b c)} {h : Fin (card c d)} →
            (comp n (comp n h g) f) ≡ comp n h (comp n g f)
  assoc (ℕ.suc n) {0F} {0F} {0F} {0F} {f} {g} {h}             = refl
  assoc (ℕ.suc n) {suc a} {suc b} {suc c} {suc d} {f} {g} {h} = assoc n

  identityˡ : ∀ n {a b : Fin n} {f : Fin (card a b)} → comp n (id b) f ≡ f
  identityˡ (ℕ.suc n) {0F} {0F} {0F}      = refl
  identityˡ (ℕ.suc n) {suc a} {suc b} {f} = identityˡ n

  identityʳ : ∀ n {a b : Fin n} {f : Fin (card a b)} → comp n f (id a) ≡ f
  identityʳ (ℕ.suc n) {0F} {0F} {0F}      = refl
  identityʳ (ℕ.suc n) {suc a} {suc b} {f} = identityʳ n

module _ (n : ℕ) where

  DiscreteShape : FinCatShape
  DiscreteShape = shapeHelper record
    { size      = n
    ; ∣_⇒_∣     = card {n}
    ; id        = id {n} _
    ; _∘_       = comp n
    ; assoc     = assoc n
    ; identityˡ = identityˡ n
    ; identityʳ = identityʳ n
    }

Discrete : ∀ n → Category _ _ _
Discrete n = FinCategory (DiscreteShape n)

module Discrete n = Category (Discrete n)
