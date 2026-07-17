{-# OPTIONS --without-K --safe #-}

module Categories.Tactic.Monoidal.Free where

open import Level using (Level)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

-- Free structural expressions for monoidal coherence.  These are the objects
-- and arrows generated only by atoms, the monoidal unit, tensor, associators,
-- and unitors.
module Free {a : Level} (Atom : Set a) where

  infixr 9 _⊗_

  data Ob : Set a where
    ‹_› : Atom → Ob
    I   : Ob
    _⊗_ : Ob → Ob → Ob

  infixr 9 _∘_
  infixr 10 _⊗₁_

  data _⇒_ : Ob → Ob → Set a where
    idₘ  : ∀ {X}     → X ⇒ X
    _∘_  : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
    _⊗₁_ : ∀ {X Y Z W} → X ⇒ Y → Z ⇒ W → (X ⊗ Z) ⇒ (Y ⊗ W)
    α⇒   : ∀ {X Y Z} → ((X ⊗ Y) ⊗ Z) ⇒ (X ⊗ (Y ⊗ Z))
    α⇐   : ∀ {X Y Z} → (X ⊗ (Y ⊗ Z)) ⇒ ((X ⊗ Y) ⊗ Z)
    λ⇒   : ∀ {X} → (I ⊗ X) ⇒ X
    λ⇐   : ∀ {X} → X ⇒ (I ⊗ X)
    ρ⇒   : ∀ {X} → (X ⊗ I) ⇒ X
    ρ⇐   : ∀ {X} → X ⇒ (X ⊗ I)

  invert : ∀ {X Y} → X ⇒ Y → Y ⇒ X
  invert idₘ       = idₘ
  invert (g ∘ f)   = invert f ∘ invert g
  invert (f ⊗₁ g)  = invert f ⊗₁ invert g
  invert α⇒        = α⇐
  invert α⇐        = α⇒
  invert λ⇒        = λ⇐
  invert λ⇐        = λ⇒
  invert ρ⇒        = ρ⇐
  invert ρ⇐        = ρ⇒

  nf : Ob → List Atom
  nf ‹ x ›   = x ∷ []
  nf I       = []
  nf (X ⊗ Y) = nf X ++ nf Y

  ⌜_⌝ : List Atom → Ob
  ⌜ [] ⌝     = I
  ⌜ x ∷ xs ⌝ = ‹ x › ⊗ ⌜ xs ⌝

  nf-⌜⌝ : (w : List Atom) → nf ⌜ w ⌝ ≡ w
  nf-⌜⌝ []       = refl
  nf-⌜⌝ (x ∷ xs) = cong (x ∷_) (nf-⌜⌝ xs)

  module NormalForm where
    assocₙ : (X Y Z : Ob) → nf ((X ⊗ Y) ⊗ Z) ≡ nf (X ⊗ (Y ⊗ Z))
    assocₙ X Y Z = ++-assoc (nf X) (nf Y) (nf Z)

    assocₙ⁻¹ : (X Y Z : Ob) → nf (X ⊗ (Y ⊗ Z)) ≡ nf ((X ⊗ Y) ⊗ Z)
    assocₙ⁻¹ X Y Z = sym (assocₙ X Y Z)

    unitʳₙ : (X : Ob) → nf (X ⊗ I) ≡ nf X
    unitʳₙ X = ++-identityʳ (nf X)

    unitʳₙ⁻¹ : (X : Ob) → nf X ≡ nf (X ⊗ I)
    unitʳₙ⁻¹ X = sym (unitʳₙ X)

  ⇒⇒nf : ∀ {X Y} → X ⇒ Y → nf X ≡ nf Y
  ⇒⇒nf idₘ              = refl
  ⇒⇒nf (g ∘ f)          = trans (⇒⇒nf f) (⇒⇒nf g)
  ⇒⇒nf (f ⊗₁ g)         = cong₂ _++_ (⇒⇒nf f) (⇒⇒nf g)
  ⇒⇒nf (α⇒ {X} {Y} {Z}) = NormalForm.assocₙ X Y Z
  ⇒⇒nf (α⇐ {X} {Y} {Z}) = NormalForm.assocₙ⁻¹ X Y Z
  ⇒⇒nf λ⇒               = refl
  ⇒⇒nf λ⇐               = refl
  ⇒⇒nf (ρ⇒ {X})         = NormalForm.unitʳₙ X
  ⇒⇒nf (ρ⇐ {X})         = NormalForm.unitʳₙ⁻¹ X
