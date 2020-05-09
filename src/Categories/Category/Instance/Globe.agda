{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Globe where

open import Level using (Level; zero)
open import Relation.Binary using (IsEquivalence; module IsEquivalence)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)

open import Categories.Category.Core

data GlobeHom : (m n : ℕ) → Set where
  I : ∀ {place : ℕ} → GlobeHom place place
  σ : ∀ {n m : ℕ} → GlobeHom (suc n) m → GlobeHom n m
  τ : ∀ {n m : ℕ} → GlobeHom (suc n) m → GlobeHom n m

data GlobeEq : {m n : ℕ} → GlobeHom m n → GlobeHom m n → Set where
  both-I : ∀ {m} → GlobeEq {m} {m} I I
  both-σ : ∀ {m n x y} → GlobeEq {m} {n} (σ x) (σ y)
  both-τ : ∀ {m n x y} → GlobeEq {m} {n} (τ x) (τ y)

GlobeEquiv : ∀ {m n} → IsEquivalence (GlobeEq {m} {n})
GlobeEquiv = record { refl = refl; sym = sym; trans = trans }
  where
  refl : ∀ {m n} {x : GlobeHom m n} → GlobeEq x x
  refl {x = I} = both-I
  refl {x = σ y} = both-σ
  refl {x = τ y} = both-τ
  sym : ∀ {m n} {x y : GlobeHom m n} → GlobeEq x y → GlobeEq y x
  sym both-I = both-I
  sym both-σ = both-σ
  sym both-τ = both-τ
  trans : ∀ {m n} {x y z : GlobeHom m n} → GlobeEq x y → GlobeEq y z → GlobeEq x z
  trans both-I y∼z = y∼z
  trans both-σ both-σ = both-σ
  trans both-τ both-τ = both-τ

infixl 7 _⊚_

_⊚_ : ∀ {l m n} → GlobeHom m n → GlobeHom l m → GlobeHom l n
x ⊚ I = x
x ⊚ σ y = σ (x ⊚ y)
x ⊚ τ y = τ (x ⊚ y)

Globe : Category Level.zero Level.zero Level.zero
Globe = record
  { Obj       = ℕ
  ; _⇒_       = GlobeHom
  ; _≈_       = GlobeEq
  ; id        = I
  ; _∘_       = _⊚_
  ; assoc     = λ {_ _ _ _ f g h} → assoc {f = f} {g} {h}
  ; sym-assoc = λ {_ _ _ _ f g h} → GlobeEquiv.sym (assoc {f = f} {g} {h})
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = GlobeEquiv
  ; ∘-resp-≈  = ∘-resp-≡
  }
  where
  module GlobeEquiv {m n} = IsEquivalence (GlobeEquiv {m} {n})
  assoc : ∀ {A B C D} {f : GlobeHom A B} {g : GlobeHom B C} {h : GlobeHom C D} → GlobeEq ((h ⊚ g) ⊚ f) (h ⊚ (g ⊚ f))
  assoc {f = I} = refl
    where open IsEquivalence GlobeEquiv
  assoc {f = σ y} = both-σ
  assoc {f = τ y} = both-τ
  identityˡ : ∀ {A B} {f : GlobeHom A B} → GlobeEq (I ⊚ f) f
  identityˡ {f = I} = both-I
  identityˡ {f = σ y} = both-σ
  identityˡ {f = τ y} = both-τ
  identityʳ : ∀ {A B} {f : GlobeHom A B} → GlobeEq (f ⊚ I) f
  identityʳ = IsEquivalence.refl GlobeEquiv
  identity² : {m : ℕ} → GlobeEq {m} (I ⊚ I) I
  identity² = both-I
  ∘-resp-≡ : ∀ {A B C} {f h : GlobeHom B C} {g i : GlobeHom A B} → GlobeEq f h → GlobeEq g i → GlobeEq (f ⊚ g) (h ⊚ i)
  ∘-resp-≡ f∼h both-I = f∼h
  ∘-resp-≡ f∼h both-σ = both-σ
  ∘-resp-≡ f∼h both-τ = both-τ
