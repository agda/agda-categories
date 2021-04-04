{-# OPTIONS --without-K --safe #-}

module Relation.Binary.PropositionalEquality.Subst.Properties where

-- Properties of 'subst' onto binary relations.

open import Level
open import Function using (_$_; flip) renaming (id to idFun; _∘_ to _⊚_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

private
  variable
    ℓ ℓ₁ ℓ₂ t t₁ t₂ o : Level

-- Two shorthands:  transport the domain or codomain of a relation along an equality.
module Shorthands {O : Set o} (R : Rel O ℓ) where
  infixr 9 _◂_
  infixl 9 _▸_

  _◂_ : ∀ {A B C} → A ≡ B → R B C → R A C
  p ◂ f = subst (flip R _) (sym p) f

  _▸_ : ∀ {A B C} → R A B → B ≡ C → R A C
  f ▸ p = subst (R _) p f

  -- Some simple properties of transports
module Transport {O : Set o} (R : Rel O ℓ) where
  open Shorthands R public

  ◂-▸-id : ∀ {A} (f : R A A) → refl ◂ f ≡ f ▸ refl
  ◂-▸-id f = refl

  ◂-▸-comm : ∀ {A B C D} (p : A ≡ B) (f : R B C) (q : C ≡ D) →
             (p ◂ (f ▸ q)) ≡ ((p ◂ f) ▸ q)
  ◂-▸-comm refl f refl = refl

  ◂-assocˡ : ∀ {A B C D} (p : A ≡ B) {q : B ≡ C} (f : R C D) →
            p ◂ q ◂ f ≡ (trans p q) ◂ f
  ◂-assocˡ refl {refl} f = refl

  ▸-assocʳ : ∀ {A B C D} (f : R A B) {p : B ≡ C} (q : C ≡ D) →
            f ▸ p ▸ q ≡ f ▸ trans p q
  ▸-assocʳ f {refl} refl = refl

-- If we have a relation Q over a relation R, we can transport over that too
module TransportOverQ {O : Set o} (R : Rel O ℓ) (Q : {X Y : O} → Rel (R X Y) t)  where
  open Transport R

  ◂-resp-≈ : ∀ {A B C} (p : A ≡ B) {f g : R B C} → Q f g → Q (p ◂ f) (p ◂ g)
  ◂-resp-≈ refl f≈g = f≈g

  ▸-resp-≈ : ∀ {A B C} {f g : R A B} → Q f g → (p : B ≡ C) → Q (f ▸ p) (g ▸ p)
  ▸-resp-≈ f≈g refl = f≈g

-- Given two relations and a homomorphism between them,
-- congruence properties over subst
module TransportMor {O₁ O₂ : Set o}
  (R₁ : Rel O₁ ℓ) (R₂ : Rel O₂ t)
  (M₀       : O₁ → O₂)
  (M₁       : ∀ {A B} → R₁ A B → R₂ (M₀ A) (M₀ B)) where

  open Shorthands R₁
  open Shorthands R₂ renaming (_◂_ to _◃_; _▸_ to _▹_)

  M-resp-▸ : ∀ {A B C} (f : R₁ A B) (p : B ≡ C) →
             M₁ (f ▸ p) ≡ M₁ f ▹ cong M₀ p
  M-resp-▸ f refl = refl

  M-resp-◂ : ∀ {A B C} (p : A ≡ B) (f : R₁ B C) →
             M₁ (p ◂ f) ≡ cong M₀ p ◃ M₁ f
  M-resp-◂ refl f = refl


-- Transports on paths
module TransportStar {O : Set o} (R : Rel O ℓ) where
  open Shorthands (Star R) public renaming
    ( _◂_ to _◂*_
    ; _▸_ to _▸*_
    )
  open Shorthands R

  -- Lemmas relating transports to path operations.

  ◂*-▸*-ε : {A B : O} (p : A ≡ B) → ε ▸* p ≡ p ◂* ε
  ◂*-▸*-ε refl = refl

  ◂*-◅ : {A B C D : O} (p : A ≡ B) (f : R B C) (fs : Star R C D) →
         p ◂* (f ◅ fs) ≡ (p ◂ f) ◅ fs
  ◂*-◅ refl f fs = refl

  ◅-▸* : {A B C D : O} (f : R A B) (fs : Star R B C) (p : C ≡ D) →
         (f ◅ fs) ▸* p ≡ f ◅ (fs ▸* p)
  ◅-▸* f fs refl = refl

  ◅-◂*-▸ : {A B C D : O} (f : R A B) (p : B ≡ C) (fs : Star R C D) →
           _≡_ {_} {Star R A D} (f ◅ (p ◂* fs)) ((f ▸ p) ◅ fs)
  ◅-◂*-▸ f refl fs = refl
