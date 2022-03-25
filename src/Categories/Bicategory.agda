{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory where

open import Level
open import Data.Product using (_,_)
open import Relation.Binary using (Rel)

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal.Instance.Cats using (module Product)
open import Categories.Enriched.Category using () renaming (Category to Enriched)
open import Categories.Functor using (module Functor)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

-- https://ncatlab.org/nlab/show/bicategory
-- notice that some axioms in nLab are inconsistent. they have been fixed in this definition.
record Bicategory o ℓ e t : Set (suc (o ⊔ ℓ ⊔ e ⊔ t)) where
  field
    enriched : Enriched (Product.Cats-Monoidal {o} {ℓ} {e}) t

  open Enriched enriched public
  module hom {A B} = Category (hom A B)
  module ComHom {A B} = Commutation (hom A B)

  infix 4 _⇒₁_ _⇒₂_ _≈_
  infixr 7 _∘ᵥ_ _∘₁_
  infixr 9 _▷_
  infixl 9 _◁_
  infixr 11 _⊚₀_ _⊚₁_  _∘ₕ_

  _⇒₁_ : Obj → Obj → Set o
  A ⇒₁ B = Category.Obj (hom A B)

  _⇒₂_ : {A B : Obj} → A ⇒₁ B → A ⇒₁ B → Set ℓ
  _⇒₂_ = hom._⇒_

  _⊚₀_ : {A B C : Obj} → B ⇒₁ C → A ⇒₁ B → A ⇒₁ C
  f ⊚₀ g = Functor.F₀ ⊚ (f , g)

  _⊚₁_ : {A B C : Obj} {f h : B ⇒₁ C} {g i : A ⇒₁ B} → f ⇒₂ h → g ⇒₂ i → f ⊚₀ g ⇒₂ h ⊚₀ i
  α ⊚₁ β = Functor.F₁ ⊚ (α , β)

  _≈_ : {A B : Obj} {f g : A ⇒₁ B} → Rel (f ⇒₂ g) e
  _≈_ = hom._≈_

  id₁ : {A : Obj} → A ⇒₁ A
  id₁ {_} = Functor.F₀ id _

  id₂ : {A B : Obj} {f : A ⇒₁ B} → f ⇒₂ f
  id₂ {A} {B} = Category.id (hom A B)

  -- 1-cell composition
  _∘₁_ : {A B C : Obj} → B ⇒₁ C → A ⇒₁ B → A ⇒₁ C
  _∘₁_ = _⊚₀_

  -- horizontal composition
  _∘ₕ_ : {A B C : Obj} {f h : B ⇒₁ C} {g i : A ⇒₁ B} → f ⇒₂ h → g ⇒₂ i → f ⊚₀ g ⇒₂ h ⊚₀ i
  _∘ₕ_ = _⊚₁_

  -- vertical composition
  _∘ᵥ_ : {A B : Obj} {f g h : A ⇒₁ B} (α : g ⇒₂ h) (β : f ⇒₂ g) → f ⇒₂ h
  _∘ᵥ_ = hom._∘_

  _◁_ : {A B C : Obj} {g h : B ⇒₁ C} (α : g ⇒₂ h) (f : A ⇒₁ B) → g ∘₁ f ⇒₂ h ∘₁ f
  α ◁ _ = α ⊚₁ id₂

  _▷_ : {A B C : Obj} {f g : A ⇒₁ B} (h : B ⇒₁ C) (α : f ⇒₂ g) → h ∘₁ f ⇒₂ h ∘₁ g
  _ ▷ α = id₂ ⊚₁ α

  private
    λ⇒ : {A B : Obj} {f : A ⇒₁ B} → id₁ ⊚₀ f hom.⇒ f
    λ⇒ {_} {_} {f} = NaturalIsomorphism.⇒.η unitˡ (_ , f)

    ρ⇒ : {A B : Obj} {f : A ⇒₁ B} → f ⊚₀ id₁ hom.⇒ f
    ρ⇒ {_} {_} {f} = NaturalIsomorphism.⇒.η unitʳ (f , _)

    α⇒ : {A B C D : Obj} {f : D ⇒₁ B} {g : C ⇒₁ D} {h : A ⇒₁ C} →
          ((f ⊚₀ g) ⊚₀ h) hom.⇒ (f ⊚₀ (g ⊚₀ h))
    α⇒ {_} {_} {_} {_} {f} {g} {h} = NaturalIsomorphism.⇒.η ⊚-assoc ((f , g) , h)

  field
    triangle : {A B C : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C} →
                 let open ComHom {A} {C} in
                 [ (g ∘₁ id₁) ∘₁ f ⇒ g ∘₁ f ]⟨
                   α⇒                 ⇒⟨ g ∘₁ id₁ ∘₁ f ⟩
                   g ▷ λ⇒
                 ≈ ρ⇒ ◁ f
                 ⟩
    pentagon : {A B C D E : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} {i : D ⇒₁ E} →
                 let open ComHom {A} {E} in
                 [ ((i ∘₁ h) ∘₁ g) ∘₁ f ⇒ i ∘₁ h ∘₁ g ∘₁ f ]⟨
                   α⇒ ◁ f                     ⇒⟨ (i ∘₁ h ∘₁ g) ∘₁ f ⟩
                   α⇒                         ⇒⟨ i ∘₁ (h ∘₁ g) ∘₁ f ⟩
                   i ▷ α⇒
                 ≈ α⇒                         ⇒⟨ (i ∘₁ h) ∘₁ g ∘₁ f ⟩
                   α⇒
                 ⟩
