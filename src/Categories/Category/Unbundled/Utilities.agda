{-# OPTIONS --without-K --safe #-}
module Categories.Category.Unbundled.Utilities where

-- various functions that are 'normally' in the Category record, but
-- are here done separately

open import Level
open import Function.Base using (flip)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category.Unbundled using (Category)

private
  variable
    o ℓ e : Level

module _ {Obj : Set o} (C : Category Obj ℓ e) where

  open Category C

  module Equiv {A B : Obj} = IsEquivalence (equiv {A} {B})

  open Equiv

  ∘-resp-≈ˡ : ∀ {A B C} {f h : B ⇒ C} {g : A ⇒ B} → f ≈ h → f ∘ g ≈ h ∘ g
  ∘-resp-≈ˡ pf = ∘-resp-≈ pf refl

  ∘-resp-≈ʳ : ∀ {A B C} {f h : A ⇒ B} {g : B ⇒ C} → f ≈ h → g ∘ f ≈ g ∘ h
  ∘-resp-≈ʳ pf = ∘-resp-≈ refl pf

  hom-setoid : ∀ {A B} → Setoid _ _
  hom-setoid {A} {B} = record
    { Carrier       = A ⇒ B
    ; _≈_           = _≈_
    ; isEquivalence = equiv
    }

  -- When a category is quantified, it is convenient to refer to the levels from a module,
  -- so we do not have to explicitly quantify over a category when universe levels do not
  -- play a big part in a proof (which is the case probably all the time).
  o-level : Level
  o-level = o

  ℓ-level : Level
  ℓ-level = ℓ

  e-level : Level
  e-level = e

  -- Reasoning combinators.  _≈⟨_⟩_ and _≈˘⟨_⟩_ from SetoidR.
  -- Also some useful combinators for doing reasoning on _∘_ chains
  module HomReasoning {A B : Obj} where
    open SetoidR (hom-setoid {A} {B}) public
    -- open Equiv {A = A} {B = B} public

    infixr 4 _⟩∘⟨_ refl⟩∘⟨_
    infixl 5 _⟩∘⟨refl
    _⟩∘⟨_ : ∀ {M} {f h : M ⇒ B} {g i : A ⇒ M} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i
    _⟩∘⟨_ = ∘-resp-≈

    refl⟩∘⟨_ : ∀ {M} {f : M ⇒ B} {g i : A ⇒ M} → g ≈ i → f ∘ g ≈ f ∘ i
    refl⟩∘⟨_ = Equiv.refl ⟩∘⟨_

    _⟩∘⟨refl : ∀ {M} {f h : M ⇒ B} {g : A ⇒ M} → f ≈ h → f ∘ g ≈ h ∘ g
    _⟩∘⟨refl = _⟩∘⟨ Equiv.refl

    -- convenient inline versions
    infix 2 ⟺
    infixr 3 _○_
    ⟺ : {f g : A ⇒ B} → f ≈ g → g ≈ f
    ⟺ = Equiv.sym
    _○_ : {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
    _○_ = Equiv.trans

  op : Category Obj ℓ e
  op = record
    { _⇒_       = flip _⇒_
    ; _≈_       = _≈_
    ; _∘_       = flip _∘_
    ; id        = id
    ; assoc     = sym-assoc
    ; sym-assoc = assoc
    ; identityˡ = identityʳ
    ; identityʳ = identityˡ
    ; identity² = identity²
    ; equiv     = equiv
    ; ∘-resp-≈  = flip ∘-resp-≈
    }
