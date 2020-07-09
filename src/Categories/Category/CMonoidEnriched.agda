{-# OPTIONS --without-K --safe #-}
module Categories.Category.CMonoidEnriched where

-- A category where the Homs are not sets, but commutative monoids
-- There are weak kind of Ab-enriched.
-- The reason to do these "by hand" is that the
-- "free commutative monoid monad", i.e. Bag, is very hard to work
-- with in type theory, so it is easier to work axiomatically.

open import Level
open import Algebra.Bundles using (CommutativeMonoid)
open import Function.Base using (flip)
open import Relation.Binary using (Rel; IsEquivalence)

open import Categories.Category.Core using (Category)

record CM-Category (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix  4 _≈_ _⇒_
  infixr 9 _∘_
  infixl 7 _+_

  open CommutativeMonoid using (_∙_; ε) renaming (Carrier to ∣_∣)
  field
    Obj : Set o
    Hom : (A B : Obj) → CommutativeMonoid ℓ e

  _⇒_ : (A B : Obj) → Set ℓ
  A ⇒ B = ∣ Hom A B ∣

  _+_ : {A B : Obj} → A ⇒ B → A ⇒ B → A ⇒ B
  _+_ {A} {B} f g = _∙_ (Hom A B) f g

  0M : {A B : Obj} → A ⇒ B
  0M {A} {B} = ε (Hom A B)

  field
    _≈_ : ∀ {A B : Obj} → Rel (A ⇒ B) e

    id  : ∀ {A} → A ⇒ A
    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C

  -- The usual categorical structure
  field
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    -- We add a symmetric proof of associativity so that the opposite category of the
    -- opposite category is definitionally equal to the original category. See how
    -- `op` is implemented.
    sym-assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    -- We add a proof of "neutral" identity proof, in order to ensure the opposite of
    -- constant functor is definitionally equal to itself.
    identity² : ∀ {A} → id ∘ id {A} ≈ id {A}
    equiv     : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

    -- preservation of additive structure
    +-resp-∘ : ∀ {A B C D} {f g : B ⇒ C} {h : A ⇒ B} {k : C ⇒ D} →
      k ∘ (f + g) ∘ h ≈ k ∘ f ∘ h + k ∘ g ∘ h

    0-resp-∘ : ∀ {A C D} {h : A ⇒ C} {k : C ⇒ D} → k ∘ 0M ∘ h ≈ 0M

Underlying : {o ℓ e : Level} → CM-Category o ℓ e → Category o ℓ e
Underlying C = record { CM-Category C }
