{-# OPTIONS --without-K --safe #-}
module Categories.LocallyGraded where

open import Level
open import Data.Unit using (tt)
open import Data.Product using (_,_)

open import Categories.Bicategory
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

import Categories.Bicategory.Extras

-- Locally Graded categories, generalized to gradation via a bicategory.
--
-- Locally graded categories are a joint generalization of displayed categories
-- and enriched categories: display can be obtained by picking a discrete
-- bicategory as your gradition, and enrichment can be obtained by asking
-- for representing objects of hom setoids.
record LocallyGraded
  {o ℓ e t}
  (B : Bicategory o ℓ e t)
  (o' ℓ' e' : Level)
  : Set (o ⊔ ℓ ⊔ e ⊔ t ⊔ suc o' ⊔ suc ℓ' ⊔ suc e') where
  open Categories.Bicategory.Extras B
  open Shorthands

  infix 4 _⇒[_]_ _≈ᵥ_
  infixr 11 _∘'_
  infix 12 _⟨_⟩

  field
    -- Displayed objects and displayed morphisms over 1-cells.
    Obj[_] : Obj → Set o'
    _⇒[_]_ : ∀ {X Y}  → Obj[ X ] → X ⇒₁ Y → Obj[ Y ] → Set ℓ'

    -- We opt to only require fibrewise setoids, as opposed to a displayed setoid.
    _≈ᵥ_ : ∀ {X Y X' Y'} {f : X ⇒₁ Y} → X' ⇒[ f ] Y' → X' ⇒[ f ] Y' → Set e'

    -- Directed transport along 2-cells in the grading category.
    _⟨_⟩ : ∀ {X Y X' Y'} {f g : X ⇒₁ Y} → X' ⇒[ g ] Y' → f ⇒₂ g → X' ⇒[ f ] Y'

  field
    -- Displayed identities and composites.
    id' : ∀ {X} {X' : Obj[ X ]} → X' ⇒[ id₁ ] X'
    _∘'_
      : ∀ {X Y Z} {X' Y' Z'}
      → {f : Y ⇒₁ Z} {g : X ⇒₁ Y}
      → Y' ⇒[ f ] Z' → X' ⇒[ g ] Y' → X' ⇒[ f ∘₁ g ] Z'

    -- Coherence for transports.
    ⟨⟩-idᵥ : ∀ {X Y X' Y'} {f : X ⇒₁ Y} {f' : X' ⇒[ f ] Y'} → f' ⟨ id₂ ⟩ ≈ᵥ f'
    ⟨⟩-∘ᵥ
      : ∀ {X Y X' Y'} {f g h : X ⇒₁ Y} {h' : X' ⇒[ h ] Y'}
      → {α : g ⇒₂ h} {β : f ⇒₂ g}
      → h' ⟨ α ∘ᵥ β ⟩ ≈ᵥ h' ⟨ α ⟩ ⟨ β ⟩
    -- We also need to ensure that identities and composites are stable under
    -- transport.
    ⟨⟩-idₕ
      : ∀ {X} {X' : Obj[ X ]} {α : id₁ ⇒₂ id₁}
      → id' {X' = X'} ⟨ α ⟩ ≈ᵥ id' {X' = X'}
    ⟨⟩-∘ₕ
      : ∀ {X Y Z X' Y' Z'} {f h : Y ⇒₁ Z} {g k : X ⇒₁ Y}
      → {h' : Y' ⇒[ h ] Z'} {k' : X' ⇒[ k ] Y'}
      → {α : f ⇒₂ h} {β : g ⇒₂ k}
      → (h' ∘' k') ⟨ α ∘ₕ β ⟩ ≈ᵥ h' ⟨ α ⟩ ∘' k' ⟨ β ⟩

    -- Left identities. Note that the second proof is actually redundant,
    -- but we want op to be a definitional involution!
    identityˡ'
      : ∀ {X Y X' Y'} {f : X ⇒₁ Y} {f' : X' ⇒[ f ] Y'}
      → id' ∘' f' ≈ᵥ f' ⟨ λ⇒ ⟩
    sym-identityˡ'
      : ∀ {X Y X' Y'} {f : X ⇒₁ Y} {f' : X' ⇒[ f ] Y'}
      → f' ≈ᵥ (id' ∘' f') ⟨ λ⇐ ⟩

    -- Right identities.
    identityʳ'
      : ∀ {X Y X' Y'} {f : X ⇒₁ Y} {f' : X' ⇒[ f ] Y'}
      → f' ∘' id' ≈ᵥ f' ⟨ ρ⇒ ⟩
    sym-identityr'
      : ∀ {X Y X' Y'} {f : X ⇒₁ Y} {f' : X' ⇒[ f ] Y'}
      → f' ≈ᵥ (f' ∘' id') ⟨ ρ⇐ ⟩

    -- Associativity.
    assoc'
      : ∀ {W X Y Z W' X' Y' Z'}
      → {f : Y ⇒₁ Z} {g : X ⇒₁ Y} {h : W ⇒₁ X}
      → {f' : Y' ⇒[ f ] Z'} {g' : X' ⇒[ g ] Y'} {h' : W' ⇒[ h ] X'}
      → (f' ∘' g') ∘' h' ≈ᵥ (f' ∘' (g' ∘' h')) ⟨ α⇒ ⟩
    sym-assoc'
      : ∀ {W X Y Z W' X' Y' Z'}
      → {f : Y ⇒₁ Z} {g : X ⇒₁ Y} {h : W ⇒₁ X}
      → {f' : Y' ⇒[ f ] Z'} {g' : X' ⇒[ g ] Y'} {h' : W' ⇒[ h ] X'}
      → f' ∘' (g' ∘' h') ≈ᵥ ((f' ∘' g') ∘' h') ⟨ α⇐ ⟩
