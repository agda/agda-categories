{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory where

open import Level
open import Data.Product using (Σ; _,_)
open import Relation.Binary using (Rel)

open import Categories.Category
open import Categories.Category.Monoidal.Instance.Cats using (module Product)
open import Categories.Category.Monoidal.Enriched
open import Categories.Category.Instance.Cats
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Bifunctor.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
import Categories.Morphism as Mor

-- https://ncatlab.org/nlab/show/bicategory
-- notice that some axioms in nLab is inconsistent. they have been fixed in this definition.
record Bicategory o ℓ e t : Set (suc (o ⊔ ℓ ⊔ e ⊔ t)) where
  field
    enriched : Enriched (Product.Cats-Monoidal {o} {ℓ} {e}) t

  open Enriched enriched public
  module Cats = Category (Cats o ℓ e)
  module hom {A B} = Category (hom A B)  

  open Functor

  module ⊚ {A B C}          = Functor (⊚ {A} {B} {C})
  module ⊚-assoc {A B C D}  = NaturalIsomorphism (⊚-assoc {A} {B} {C} {D})
  module unitˡ {A B}        = NaturalIsomorphism (unitˡ {A} {B})
  module unitʳ {A B}        = NaturalIsomorphism (unitʳ {A} {B})
  module id {A}             = Functor (id A)

  infix 4 _⇒₁_ _⇒₂_ _≈_
  infixr 7 _◁_ _▷_
  infixr 9 _∘ₕ_ _∘ᵥ_
  infixr 11 _⊚₀_ _⊚₁_

  _⇒₁_ : Obj → Obj → Set o
  A ⇒₁ B = Category.Obj (hom A B)

  _⇒₂_ : ∀ {A B} → A ⇒₁ B → A ⇒₁ B → Set ℓ
  _⇒₂_ = hom._⇒_

  _⊚₀_ : ∀ {A B C} → B ⇒₁ C → A ⇒₁ B → A ⇒₁ C
  f ⊚₀ g = ⊚.F₀ (f , g)

  _⊚₁_ : ∀ {A B C} {f h : B ⇒₁ C} {g i : A ⇒₁ B} → f ⇒₂ h → g ⇒₂ i → f ⊚₀ g ⇒₂ h ⊚₀ i
  α ⊚₁ β = ⊚.F₁ (α , β)

  _≈_ : ∀ {A B} {f g : A ⇒₁ B} → Rel (f ⇒₂ g) e
  _≈_ = hom._≈_

  id₁ : ∀ {A} → A ⇒₁ A
  id₁ {_} = id.F₀ _

  id₂ : ∀ {A B} {f : A ⇒₁ B} → f ⇒₂ f
  id₂ = hom.id

  -- horizontal composition
  _∘ₕ_ : ∀ {A B C} → B ⇒₁ C → A ⇒₁ B → A ⇒₁ C
  _∘ₕ_ = _⊚₀_

  -- vertical composition
  _∘ᵥ_ : ∀ {A B} {f g h : A ⇒₁ B} (α : g ⇒₂ h) (β : f ⇒₂ g) → f ⇒₂ h
  _∘ᵥ_ = hom._∘_

  _◁_ : ∀ {A B C} {g h : B ⇒₁ C} (α : g ⇒₂ h) (f : A ⇒₁ B) → g ∘ₕ f ⇒₂ h ∘ₕ f
  α ◁ f = α ⊚₁ id₂

  _▷_ : ∀ {A B C} {f g : A ⇒₁ B} (h : B ⇒₁ C) (α : f ⇒₂ g) → h ∘ₕ f ⇒₂ h ∘ₕ g
  h ▷ α = id₂ ⊚₁ α

  unitorˡ : ∀ {A B} {f : A ⇒₁ B} → Mor._≅_ (hom A B) (id₁ ∘ₕ f) f
  unitorˡ {_} {_} {f} = record
    { from = unitˡ.⇒.η (_ , f)
    ; to   = unitˡ.⇐.η (_ , f)
    ; iso  = unitˡ.iso (_ , f)
    }

  module unitorˡ {A B f} = Mor._≅_ (unitorˡ {A} {B} {f})

  unitorʳ : ∀ {A B} {f : A ⇒₁ B} → Mor._≅_ (hom A B) (f ∘ₕ id₁) f
  unitorʳ {_} {_} {f} = record
    { from = unitʳ.⇒.η (f , _)
    ; to   = unitʳ.⇐.η (f , _)
    ; iso  = unitʳ.iso (f , _)
    }

  module unitorʳ {A B f} = Mor._≅_ (unitorʳ {A} {B} {f})

  associator : ∀ {A B C D} {f : D ⇒₁ B} {g : C ⇒₁ D} {h : A ⇒₁ C} →  Mor._≅_ (hom A B) ((f ∘ₕ g) ∘ₕ h) (f ∘ₕ g ∘ₕ h)
  associator {_} {_} {_} {_} {f} {g} {h} = record
    { from = ⊚-assoc.⇒.η ((f , g) , h)
    ; to   = ⊚-assoc.⇐.η ((f , g) , h)
    ; iso  = ⊚-assoc.iso ((f , g) , h)
    }

  module associator {A B C D} {f : C ⇒₁ B} {g : D ⇒₁ C} {h} = Mor._≅_ (associator {A = A} {B = B} {f = f} {g = g} {h = h})

  open hom.Commutation

  field
    triangle : ∀ {A B C} {f : A ⇒₁ B} {g : B ⇒₁ C} →
                 [ (g ⊚₀ id₁) ⊚₀ f ⇒ g ⊚₀ f ]⟨
                   associator.from          ⇒⟨ g ⊚₀ id₁ ⊚₀ f ⟩
                   g ▷ unitorˡ.from
                 ≈ unitorʳ.from ◁ f
                 ⟩
    pentagon : ∀ {A B C D E} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} {i : D ⇒₁ E} →
                 [ ((i ⊚₀ h) ⊚₀ g) ⊚₀ f ⇒ i ⊚₀ h ⊚₀ g ⊚₀ f ]⟨
                   associator.from ◁ f                     ⇒⟨ (i ⊚₀ h ⊚₀ g) ⊚₀ f ⟩
                   associator.from                         ⇒⟨ i ⊚₀ (h ⊚₀ g) ⊚₀ f ⟩
                   i ▷ associator.from
                 ≈ associator.from                         ⇒⟨ (i ⊚₀ h) ⊚₀ g ⊚₀ f ⟩
                   associator.from
                 ⟩

  private
    variable
      A B C D : Obj
      f g h i : A ⇒₁ B
      α β γ : f ⇒₂ g

  -⊚_ : C ⇒₁ A → Functor (hom A B) (hom C B)
  -⊚_ = appʳ ⊚

  _⊚- : B ⇒₁ C → Functor (hom A B) (hom A C)
  _⊚- = appˡ ⊚

  identity₂ˡ : id₂ ∘ᵥ α ≈ α
  identity₂ˡ = hom.identityˡ
  
  identity₂ʳ : α ∘ᵥ id₂ ≈ α
  identity₂ʳ = hom.identityʳ

  assoc₂ : (α ∘ᵥ β) ∘ᵥ γ ≈ α ∘ᵥ β ∘ᵥ γ
  assoc₂ = hom.assoc

  id₂◁ : id₂ {f = g} ◁ f ≈ id₂
  id₂◁ = ⊚.identity

  ◁id₂ : f ▷ id₂ {f = g} ≈ id₂
  ◁id₂ = ⊚.identity

  open hom.HomReasoning

  ∘ᵥ-distr-◁ : (α ◁ f) ∘ᵥ (β ◁ f) ≈ (α ∘ᵥ β) ◁ f
  ∘ᵥ-distr-◁ {f = f} = ⟺ (Functor.homomorphism (-⊚ f))

  ∘ᵥ-distr-▷ : (f ▷ α) ∘ᵥ (f ▷ β) ≈ f ▷ (α ∘ᵥ β)
  ∘ᵥ-distr-▷ {f = f} = ⟺ (Functor.homomorphism (f ⊚-))

  λ-∘ᵥ-▷ : unitorˡ.from ∘ᵥ (id₁ ▷ α) ≈ α ∘ᵥ unitorˡ.from
  λ-∘ᵥ-▷ {α = α} = begin
    unitorˡ.from ∘ᵥ (id₁ ▷ α)    ≈˘⟨ hom.∘-resp-≈ʳ (⊚.F-resp-≈ (id.identity , refl)) ⟩
    unitorˡ.from ∘ᵥ id.F₁ _ ⊚₁ α ≈⟨ unitˡ.⇒.commute (_ , α) ⟩
    α ∘ᵥ unitorˡ.from            ∎

  ρ-∘ᵥ-◁ : unitorʳ.from ∘ᵥ (α ◁ id₁) ≈ α ∘ᵥ unitorʳ.from
  ρ-∘ᵥ-◁ {α = α} = begin
    unitorʳ.from ∘ᵥ (α ◁ id₁)      ≈˘⟨ hom.∘-resp-≈ʳ (⊚.F-resp-≈ (refl , id.identity)) ⟩
    unitorʳ.from ∘ᵥ (α ⊚₁ id.F₁ _) ≈⟨ unitʳ.⇒.commute (α , _) ⟩
    α ∘ᵥ unitorʳ.from              ∎

  assoc-◁-∘ₕ : associator.to ∘ᵥ (α ◁ (g ∘ₕ f)) ≈ ((α ◁ g) ◁ f) ∘ᵥ associator.to
  assoc-◁-∘ₕ {α = α} {g = g} {f = f} = begin
    associator.to ∘ᵥ (α ◁ (g ∘ₕ f))    ≈˘⟨ hom.∘-resp-≈ʳ (⊚.F-resp-≈ (refl , ⊚.identity)) ⟩
    associator.to ∘ᵥ (α ⊚₁ id₂ ⊚₁ id₂) ≈⟨ ⊚-assoc.⇐.commute ((α , id₂) , id₂) ⟩
    ((α ◁ g) ◁ f) ∘ᵥ associator.to     ∎

  assoc-▷-◁ : associator.to ∘ᵥ (f ▷ (α ◁ g)) ≈ ((f ▷ α) ◁ g) ∘ᵥ associator.to
  assoc-▷-◁ {f = f} {α = α} {g = g} = ⊚-assoc.⇐.commute ((id₂ , α) , id₂)

  assoc-▷-∘ₕ : associator.to ∘ᵥ (g ▷ (f ▷ α)) ≈ ((g ∘ₕ f) ▷ α) ∘ᵥ associator.to
  assoc-▷-∘ₕ {g = g} {f = f} {α = α} = begin
    associator.to ∘ᵥ (g ▷ (f ▷ α))       ≈⟨ ⊚-assoc.⇐.commute ((id₂ , id₂) , α) ⟩
    ((id₂ ⊚₁ id₂) ⊚₁ α) ∘ᵥ associator.to ≈⟨ hom.∘-resp-≈ˡ (⊚.F-resp-≈ (⊚.identity , refl)) ⟩
    ((g ∘ₕ f) ▷ α) ∘ᵥ associator.to      ∎

  ◁-▷-exchg : ∀ {α : f ⇒₂ g} {β : h ⇒₂ i} → (i ▷ α) ∘ᵥ (β ◁ f) ≈ (β ◁ g) ∘ᵥ (h ▷ α)
  ◁-▷-exchg = [ ⊚ ]-commute
