{-# OPTIONS --without-K --safe #-}

module Categories.Category.Finite.Fin.Construction.Poset where

open import Data.Nat.Base using (ℕ; z≤n; s≤s)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Fin.Base using (Fin; zero; suc; _≤_; _<_)
open import Data.Fin.Patterns

open import Relation.Binary.PropositionalEquality.Core as ≡

open import Categories.Category.Finite.Fin
open import Categories.Category.Core

private
  card : ∀ {n} → Fin n → Fin n → ℕ
  card {ℕ.suc n} zero y          = 1
  card {ℕ.suc n} (suc x) zero    = 0
  card {ℕ.suc n} (suc x) (suc y) = card x y

  id : ∀ n {a : Fin n} → Fin (card a a)
  id .(ℕ.suc _) {zero} = 0F
  id (ℕ.suc n) {suc a} = id n

  comp : ∀ n {a b c : Fin n} → Fin (card b c) → Fin (card a b) → Fin (card a c)
  comp (ℕ.suc n) {0F} {b} {c} f g = 0F
  comp (ℕ.suc n) {suc a} {suc b} {suc c} f g = comp n f g

  assoc : ∀ n {a b c d : Fin n} {f : Fin (card a b)} {g : Fin (card b c)} {h : Fin (card c d)} →
              comp n (comp n h g) f ≡ comp n h (comp n g f)
  assoc (ℕ.suc n) {0F} {b} {c} {d} {f} {g} {h}                = refl
  assoc (ℕ.suc n) {suc a} {suc b} {suc c} {suc d} {f} {g} {h} = assoc n

  identityˡ : ∀ n {a b : Fin n} {f : Fin (card a b)} → comp n (id n) f ≡ f
  identityˡ (ℕ.suc n) {0F} {b} {0F} = refl
  identityˡ (ℕ.suc n) {suc a} {suc b} {f} = identityˡ n

  identityʳ : ∀ n {a b : Fin n} {f : Fin (card a b)} → comp n f (id n) ≡ f
  identityʳ (ℕ.suc n) {0F} {b} {0F}       = refl
  identityʳ (ℕ.suc n) {suc a} {suc b} {f} = identityʳ n

card-rel : ∀ {n} (x y : Fin n) → card x y ≡ 1 × x ≤ y ⊎ card x y ≡ 0 × y < x
card-rel {ℕ.suc n} 0F y       = inj₁ (refl , z≤n)
card-rel {ℕ.suc n} (suc x) 0F = inj₂ (refl , s≤s z≤n)
card-rel {ℕ.suc n} (suc x) (suc y) with card-rel x y
... | inj₁ (eq , x≤y)         = inj₁ (eq , s≤s x≤y)
... | inj₂ (eq , y<x)         = inj₂ (eq , s≤s y<x)

card-sound₁ : ∀ {n} (x y : Fin n) → card x y ≡ 1 → x ≤ y
card-sound₁ 0F 0F eq           = z≤n
card-sound₁ 0F (suc y) eq      = z≤n
card-sound₁ (suc x) (suc y) eq = s≤s (card-sound₁ x y eq)

card-sound₂ : ∀ {n} (x y : Fin n) → card x y ≡ 0 → y ≤ x
card-sound₂ (suc x) 0F eq      = z≤n
card-sound₂ (suc x) (suc y) eq = s≤s (card-sound₂ x y eq)

card-complete₁ : ∀ {n} {x y : Fin n} → x ≤ y → card x y ≡ 1
card-complete₁ {.(ℕ.suc _)} {0F} {0F} x≤y             = refl
card-complete₁ {.(ℕ.suc _)} {0F} {suc y} x≤y          = refl
card-complete₁ {.(ℕ.suc _)} {suc x} {suc y} (s≤s x≤y) = card-complete₁ x≤y

card-complete₂ : ∀ {n} {x y : Fin n} → y < x → card x y ≡ 0
card-complete₂ {.(ℕ.suc _)} {suc x} {0F} y<x          = refl
card-complete₂ {.(ℕ.suc _)} {suc x} {suc y} (s≤s y<x) = card-complete₂ y<x

module _ (size : ℕ) where

  PosetShape : FinCatShape
  PosetShape = shapeHelper record
    { size      = size
    ; ∣_⇒_∣     = card
    ; id        = id size
    ; _∘_       = comp size
    ; assoc     = assoc size
    ; identityˡ = identityˡ size
    ; identityʳ = identityʳ size
    }

Poset : ℕ → Category _ _ _
Poset size = FinCategory (PosetShape size)

module Poset size = Category (Poset size)
