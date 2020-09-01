{-# OPTIONS --without-K --safe #-}
module Categories.Category.Helper where

open import Level
open import Relation.Binary using (Rel; IsEquivalence)

open import Categories.Category.Core using (Category)

-- Since we add extra proofs in the definition of `Category` (i.e. `sym-assoc` and
-- `identity²`), we might still want to construct a `Category` in its originally
-- easier manner. Thus, this redundant definition is here to ease the construction.
private
  record CategoryHelper (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
    infix  4 _≈_ _⇒_
    infixr 9 _∘_

    field
      Obj : Set o
      _⇒_ : Rel Obj ℓ
      _≈_ : ∀ {A B} → Rel (A ⇒ B) e

      id  : ∀ {A} → (A ⇒ A)
      _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

    field
      assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
      identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
      identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
      equiv     : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
      ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

categoryHelper : ∀ {o ℓ e} → CategoryHelper o ℓ e → Category o ℓ e
categoryHelper C = record
  { Obj       = Obj
  ; _⇒_       = _⇒_
  ; _≈_       = _≈_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = assoc
  ; sym-assoc = sym assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identityˡ
  ; equiv     = equiv
  ; ∘-resp-≈  = ∘-resp-≈
  }
  where open CategoryHelper C
        module _ {A B} where
          open IsEquivalence (equiv {A} {B}) public
