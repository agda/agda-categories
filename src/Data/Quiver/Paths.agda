{-# OPTIONS --without-K --safe #-}

module Data.Quiver.Paths where

-- Paths in a Quiver.
--
-- This is almost the same as the 'paths' in a relation, as defined in
-- Relation.Binary.Construct.Closure.ReflexiveTransitive
-- but here the relation is typed, and that has to be respected. So this
-- is somewhat duplicated

open import Level
open import Data.Quiver
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqR
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

module Paths {o ℓ e : Level} (Q : Quiver o ℓ e) where
  open Quiver Q hiding (setoid)

  private
    variable
      A B : Obj

  infix 4 _≈*_
  data _≈*_ : (p q : Star _⇒_ A B) → Set (o ⊔ ℓ ⊔ e) where
      ε : {A : Obj} → _≈*_ {A} ε ε
      _◅_ : {A B C : Obj} {x y : A ⇒ B} {p q : Star _⇒_ B C} (x≈y : x ≈ y) (p≈q : p ≈* q) → x ◅ p ≈* y ◅ q

  refl : {p : Star _⇒_ A B} → p ≈* p
  refl {p = ε} = ε
  refl {p = x ◅ p} = Equiv.refl ◅ refl

  sym : {p q : Star _⇒_ A B} → p ≈* q → q ≈* p
  sym ε = ε
  sym (x≈y ◅ eq) = Equiv.sym x≈y ◅ sym eq

  ≡⇒≈* : {p q : Star _⇒_ A B} → p ≡ q → p ≈* q
  ≡⇒≈* ≡.refl = refl

  ≡⇒≈ : {p q : A ⇒ B} → p ≡ q → p ≈ q
  ≡⇒≈ ≡.refl = Equiv.refl

  trans : {p q r : Star _⇒_ A B} → p ≈* q → q ≈* r → p ≈* r
  trans ε ε = ε
  trans (x≈y ◅ ss) (y≈z ◅ tt) = Equiv.trans x≈y y≈z ◅ trans ss tt

  isEquivalence : IsEquivalence (λ (p q : Star _⇒_ A B) → p ≈* q)
  isEquivalence = record { refl = refl ; sym = sym ; trans = trans }

  setoid : Obj → Obj → Setoid (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
  setoid A B = record { _≈_ = _≈*_ ; isEquivalence = isEquivalence {A} {B} }

  -- convenient to define here
  --
  -- FIXME: this should go into the standard library at
  -- Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
  ◅◅-identityʳ : (f : Star _⇒_ A B) → f ◅◅ ε ≈* f
  ◅◅-identityʳ ε = ε
  ◅◅-identityʳ (x ◅ f) = Equiv.refl ◅ ◅◅-identityʳ f

  module PathEqualityReasoning {A B} where
    open EqR (setoid A B) public
