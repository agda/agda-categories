{-# OPTIONS --without-K --safe #-}

module Categories.Category.Finite.Fin where

open import Level
open import Data.Nat using (ℕ)
open import Data.Fin
open import Data.Fin.Properties
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as ≡

open import Categories.Category

-- a shape of a finite catgegory
--
-- Classically, a finite category has a finite number of objects and a finite number
-- of morphisms. However, in this library, we cannot conveniently count the number of
-- objects and morphisms, because morphisms are identified up to the underlying
-- equivalence and objects have no general notion of identity. As a result, the
-- classical definition fails.
--
-- Nevetheless, if we know precisely what the objects and morphisms are, then we might
-- be able to count them. As a result, finite categories are just adjoint equivalent
-- to some category with a finite shape. Motivated by this idea, we can consider a
-- category with both objects and morphisms represented by Fin. We know Fin has
-- decidable equality and consequently also UIP. We additionally require categorical
-- axioms and thus ensures all shapes form categories.
record FinCatShape (n : ℕ) (∣_⇒_∣ : Fin n → Fin n → ℕ) : Set where
  infixr 9 _∘_

  _⇒_ : Rel (Fin n) 0ℓ
  a ⇒ b = Fin ∣ a ⇒ b ∣

  field
    id  : ∀ {a} → a ⇒ a
    _∘_ : ∀ {a b c} → b ⇒ c → a ⇒ b → a ⇒ c

  field
    assoc     : ∀ {a b c d} {f : a ⇒ b} {g : b ⇒ c} {h : c ⇒ d} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    identityˡ : ∀ {a b} {f : a ⇒ b} → id ∘ f ≡ f
    identityʳ : ∀ {a b} {f : a ⇒ b} → f ∘ id ≡ f

FinCategory : ∀ {n card} → FinCatShape n card → Category 0ℓ 0ℓ 0ℓ
FinCategory {n} {card} s = record
  { Obj       = Fin n
  ; _⇒_       = _⇒_
  ; _≈_       = _≡_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = assoc
  ; sym-assoc = sym assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identityˡ
  ; equiv     = ≡.isEquivalence
  ; ∘-resp-≈  = cong₂ _∘_
  }
  where open FinCatShape s
