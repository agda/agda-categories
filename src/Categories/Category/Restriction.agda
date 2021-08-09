{-# OPTIONS --without-K --safe #-}

-- Defines Restriction Category
--   https://ncatlab.org/nlab/show/restriction+category
-- but see also
--   https://github.com/jmchapman/restriction-categories

-- Notation choice: one of the interpretations is that the
-- restriction structure captures the "domain of definedness"
-- of a morphism, as a (partial) identity. As this is positive
-- information, we will use f ↓ (as a postfix operation) to
-- denote this. Note that computability theory uses the same
-- notation to mean definedness.

-- Note, as we're working in Setoid-Enriched Categories, we need
-- to add an explicit axiom, that ↓ preserves ≈
module Categories.Category.Restriction where

open import Level using (Level; _⊔_)

open import Categories.Category.Core using (Category)

private
  variable
    o ℓ e : Level

record Restriction (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C using (Obj; _⇒_; _∘_; _≈_; id)

  field
    _↓ :  {A B : Obj} → A ⇒ B → A ⇒ A
    -- partial identity on the right
    pidʳ : {A B : Obj} {f : A ⇒ B} → f ∘ f ↓ ≈ f
    -- the domain-of-definition arrows commute
    ↓-comm : {A B C : Obj} {f : A ⇒ B} {g : A ⇒ C} → f ↓ ∘ g ↓ ≈ g ↓ ∘ f ↓
    -- domain-of-definition denests (on the right)
    ↓-denestʳ : {A B C : Obj} {f : A ⇒ B} {g : A ⇒ C} → (g ∘ f ↓) ↓ ≈ g ↓ ∘ f ↓
    -- domain-of-definition has a skew-commutative law
    ↓-skew-comm : {A B C : Obj} {g : A ⇒ B} {f : C ⇒ A} → g ↓ ∘ f ≈ f ∘ (g ∘ f) ↓
    -- and the new axiom, ↓ is a congruence
    ↓-cong : {A B : Obj} {f g : A ⇒ B} → f ≈ g → f ↓ ≈ g ↓

  -- it is convenient to define the total predicate in this context
  total : {A B : Obj} (f : A ⇒ B) → Set e
  total f = f ↓ ≈ id
