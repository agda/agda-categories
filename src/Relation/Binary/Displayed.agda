{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Displayed where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)

private
  variable
    a ℓ a′ ℓ′ : Level

record IsDisplayedEquivalence
  {A : Set a} {_≈_ : Rel A ℓ} (isEquivalence : IsEquivalence _≈_)
  {A′ : A → Set a′} (_≈[_]_ : ∀ {x y} → A′ x → x ≈ y → A′ y → Set ℓ′) : Set (a ⊔ ℓ ⊔ a′ ⊔ ℓ′)
  where
  open IsEquivalence isEquivalence
  field
    refl′ : ∀ {x} {x′ : A′ x} → x′ ≈[ refl ] x′
    sym′ : ∀ {x y} {x′ : A′ x} {y′ : A′ y} {p : x ≈ y} → x′ ≈[ p ] y′ → y′ ≈[ sym p ] x′
    trans′ : ∀ {x y z} {x′ : A′ x} {y′ : A′ y} {z′ : A′ z} {p : x ≈ y} {q : y ≈ z} → x′ ≈[ p ] y′ → y′ ≈[ q ] z′ → x′ ≈[ trans p q ] z′

record DisplayedSetoid (B : Setoid a ℓ) a′ ℓ′ : Set (a ⊔ ℓ ⊔ suc (a′ ⊔ ℓ′)) where
  open Setoid B
  field
    Carrier′ : Carrier → Set a′
    _≈[_]_ : ∀ {x y} → Carrier′ x → x ≈ y → Carrier′ y → Set ℓ′
    isDisplayedEquivalence : IsDisplayedEquivalence isEquivalence _≈[_]_
  open IsDisplayedEquivalence isDisplayedEquivalence public
