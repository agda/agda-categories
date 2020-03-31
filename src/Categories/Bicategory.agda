{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory where

open import Level
open import Data.Product using (_,_)
open import Relation.Binary using (Rel)

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Instance.Cats using (module Product)
open import Categories.Enriched.Category using () renaming (Category to Enriched)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

-- https://ncatlab.org/nlab/show/bicategory
-- notice that some axioms in nLab are inconsistent. they have been fixed in this definition.
record Bicategory o ℓ e t : Set (suc (o ⊔ ℓ ⊔ e ⊔ t)) where
  field
    enriched : Enriched (Product.Cats-Monoidal {o} {ℓ} {e}) t

  open Enriched enriched public
  module hom {A B} = Category (hom A B)

  open Functor

  module ⊚ {A B C}          = Functor (⊚ {A} {B} {C})
  module ⊚-assoc {A B C D}  = NaturalIsomorphism (⊚-assoc {A} {B} {C} {D})
  module unitˡ {A B}        = NaturalIsomorphism (unitˡ {A} {B})
  module unitʳ {A B}        = NaturalIsomorphism (unitʳ {A} {B})
  module id {A}             = Functor (id {A})

  infix 4 _⇒₁_ _⇒₂_ _≈_
  infixr 7 _∘ᵥ_ _∘ₕ_
  infixr 9 _▷_
  infixl 9 _◁_
  infixr 11 _⊚₀_ _⊚₁_

  _⇒₁_ : Obj → Obj → Set o
  A ⇒₁ B = Category.Obj (hom A B)

  _⇒₂_ : {A B : Obj} → A ⇒₁ B → A ⇒₁ B → Set ℓ
  _⇒₂_ = hom._⇒_

  _⊚₀_ : {A B C : Obj} → B ⇒₁ C → A ⇒₁ B → A ⇒₁ C
  f ⊚₀ g = ⊚.F₀ (f , g)

  _⊚₁_ : {A B C : Obj} {f h : B ⇒₁ C} {g i : A ⇒₁ B} → f ⇒₂ h → g ⇒₂ i → f ⊚₀ g ⇒₂ h ⊚₀ i
  α ⊚₁ β = ⊚.F₁ (α , β)

  _≈_ : {A B : Obj} {f g : A ⇒₁ B} → Rel (f ⇒₂ g) e
  _≈_ = hom._≈_

  id₁ : {A : Obj} → A ⇒₁ A
  id₁ {_} = id.F₀ _

  id₂ : {A B : Obj} {f : A ⇒₁ B} → f ⇒₂ f
  id₂ = hom.id

  -- horizontal composition
  _∘ₕ_ : {A B C : Obj} → B ⇒₁ C → A ⇒₁ B → A ⇒₁ C
  _∘ₕ_ = _⊚₀_

  -- vertical composition
  _∘ᵥ_ : {A B : Obj} {f g h : A ⇒₁ B} (α : g ⇒₂ h) (β : f ⇒₂ g) → f ⇒₂ h
  _∘ᵥ_ = hom._∘_

  _◁_ : {A B C : Obj} {g h : B ⇒₁ C} (α : g ⇒₂ h) (f : A ⇒₁ B) → g ∘ₕ f ⇒₂ h ∘ₕ f
  α ◁ _ = α ⊚₁ id₂

  _▷_ : {A B C : Obj} {f g : A ⇒₁ B} (h : B ⇒₁ C) (α : f ⇒₂ g) → h ∘ₕ f ⇒₂ h ∘ₕ g
  _ ▷ α = id₂ ⊚₁ α

  private
    λ⇒ : {A B : Obj} {f : A ⇒₁ B} → ⊚.F₀ (id₁ , f) hom.⇒ f
    λ⇒ {_} {_} {f} = unitˡ.⇒.η (_ , f)

    ρ⇒ : {A B : Obj} {f : A ⇒₁ B} → ⊚.F₀ (f , id₁) hom.⇒ f
    ρ⇒ {_} {_} {f} = unitʳ.⇒.η (f , _)

    α⇒ : {A B C D : Obj} {f : D ⇒₁ B} {g : C ⇒₁ D} {h : A ⇒₁ C} →
         ⊚.F₀ (⊚.F₀ (f , g) , h) hom.⇒ ⊚.F₀ (f , ⊚.F₀ (g , h))
    α⇒ {_} {_} {_} {_} {f} {g} {h} = ⊚-assoc.⇒.η ((f , g) , h)

  open hom.Commutation

  field
    triangle : {A B C : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C} →
                 [ (g ∘ₕ id₁) ∘ₕ f ⇒ g ∘ₕ f ]⟨
                   α⇒                 ⇒⟨ g ∘ₕ id₁ ∘ₕ f ⟩
                   g ▷ λ⇒
                 ≈ ρ⇒ ◁ f
                 ⟩
    pentagon : {A B C D E : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} {i : D ⇒₁ E} →
                 [ ((i ∘ₕ h) ∘ₕ g) ∘ₕ f ⇒ i ∘ₕ h ∘ₕ g ∘ₕ f ]⟨
                   α⇒ ◁ f                     ⇒⟨ (i ∘ₕ h ∘ₕ g) ∘ₕ f ⟩
                   α⇒                         ⇒⟨ i ∘ₕ (h ∘ₕ g) ∘ₕ f ⟩
                   i ▷ α⇒
                 ≈ α⇒                         ⇒⟨ (i ∘ₕ h) ∘ₕ g ∘ₕ f ⟩
                   α⇒
                 ⟩
