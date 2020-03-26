{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Closure.SymmetricTransitive where

open import Level
open import Relation.Binary

private
  variable
    a ℓ ℓ′ : Level
    A B    : Set a

module _ {A : Set a} (_≤_ : Rel A ℓ) where
  private
    variable
      x y z : A

  data Plus⇔ : Rel A (a ⊔ ℓ) where
    forth  : x ≤ y → Plus⇔ x y
    back   : y ≤ x → Plus⇔ x y
    forth⁺ : x ≤ y → Plus⇔ y z → Plus⇔ x z
    back⁺  : y ≤ x → Plus⇔ y z → Plus⇔ x z

module _ {_≤_ : Rel A ℓ} {_≼_ : Rel B ℓ′} (f : A → B) (inj : _≤_ =[ f ]⇒ _≼_) where

  map : ∀ {x y} → Plus⇔ _≤_ x y → Plus⇔ _≼_ (f x) (f y)
  map (forth r)      = forth (inj r)
  map (back r)       = back (inj r)
  map (forth⁺ r rel) = forth⁺ (inj r) (map rel)
  map (back⁺ r rel)  = back⁺ (inj r) (map rel)

module _ (P : Preorder a ℓ ℓ′) where
  private
    module P = Preorder P
    open P hiding (refl; trans; isEquivalence)

  refl : Reflexive (Plus⇔ _∼_)
  refl {x} = forth P.refl

  trans : Transitive (Plus⇔ _∼_)
  trans (forth r) rel′      = forth⁺ r rel′
  trans (back r) rel′       = back⁺ r rel′
  trans (forth⁺ r rel) rel′ = forth⁺ r (trans rel rel′)
  trans (back⁺ r rel) rel′  = back⁺ r (trans rel rel′)

  sym : Symmetric (Plus⇔ _∼_)
  sym (forth r) = back r
  sym (back r) = forth r
  sym (forth⁺ r rel) = trans (sym rel) (back r)
  sym (back⁺ r rel) = trans (sym rel) (forth r)

  isEquivalence : IsEquivalence (Plus⇔ _∼_)
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  setoid : Setoid a (a ⊔ ℓ′)
  setoid = record
    { Carrier       = Carrier
    ; _≈_           = Plus⇔ _∼_
    ; isEquivalence = isEquivalence
    }

  module _ {c e} (S : Setoid c e) where
    private
      module S = Setoid S

    minimal : (f : Carrier → Setoid.Carrier S) →
              _∼_ =[ f ]⇒ Setoid._≈_ S →
              Plus⇔ _∼_ =[ f ]⇒ Setoid._≈_ S
    minimal f inj (forth r)      = inj r
    minimal f inj (back r)       = S.sym (inj r)
    minimal f inj (forth⁺ r rel) = S.trans (inj r) (minimal f inj rel)
    minimal f inj (back⁺ r rel)  = S.trans (S.sym (inj r)) (minimal f inj rel)
  
