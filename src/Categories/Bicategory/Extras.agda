{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory.Extras where

open import Data.Product using (_,_)

open import Categories.Bicategory using (Bicategory)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (appʳ; appˡ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

module Extras {o ℓ e t} (Bicat : Bicategory o ℓ e t) where
  open Bicategory Bicat
  private
    variable
      A B C D : Obj
      f g h i : A ⇒₁ B
      α β γ : f ⇒₂ g

  module ⊚ {A B C}          = Functor (⊚ {A} {B} {C})
  module ⊚-assoc {A B C D}  = NaturalIsomorphism (⊚-assoc {A} {B} {C} {D})
  module unitˡ {A B}        = NaturalIsomorphism (unitˡ {A} {B})
  module unitʳ {A B}        = NaturalIsomorphism (unitʳ {A} {B})
  module id {A}             = Functor (id {A})

  unitorˡ : {A B : Obj} {f : A ⇒₁ B} → Mor._≅_ (hom A B) (id₁ ∘ₕ f) f
  unitorˡ {_} {_} {f} = record
    { from = unitˡ.⇒.η (_ , f)
    ; to   = unitˡ.⇐.η (_ , f)
    ; iso  = unitˡ.iso (_ , f)
    }

  module unitorˡ {A B f} = Mor._≅_ (unitorˡ {A} {B} {f})

  unitorʳ : {A B : Obj} {f : A ⇒₁ B} → Mor._≅_ (hom A B) (f ∘ₕ id₁) f
  unitorʳ {_} {_} {f} = record
    { from = unitʳ.⇒.η (f , _)
    ; to   = unitʳ.⇐.η (f , _)
    ; iso  = unitʳ.iso (f , _)
    }

  module unitorʳ {A B f} = Mor._≅_ (unitorʳ {A} {B} {f})

  associator : {A B C D : Obj} {f : D ⇒₁ B} {g : C ⇒₁ D} {h : A ⇒₁ C} →  Mor._≅_ (hom A B) ((f ∘ₕ g) ∘ₕ h) (f ∘ₕ g ∘ₕ h)
  associator {_} {_} {_} {_} {f} {g} {h} = record
    { from = ⊚-assoc.⇒.η ((f , g) , h)
    ; to   = ⊚-assoc.⇐.η ((f , g) , h)
    ; iso  = ⊚-assoc.iso ((f , g) , h)
    }

  module associator {A B C D} {f : C ⇒₁ B} {g : D ⇒₁ C} {h} = Mor._≅_ (associator {A = A} {B = B} {f = f} {g = g} {h = h})

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

  ▷id₂ : f ▷ id₂ {f = g} ≈ id₂
  ▷id₂ = ⊚.identity

  open hom.HomReasoning
  open hom.Equiv
  private
    module MR′ {A} {B} where
      open MR (hom A B) using (conjugate-to) public
      open Mor (hom A B) using (module ≅) public
    open MR′

  ∘ᵥ-distr-◁ : (α ◁ f) ∘ᵥ (β ◁ f) ≈ (α ∘ᵥ β) ◁ f
  ∘ᵥ-distr-◁ {f = f} = ⟺ (Functor.homomorphism (-⊚ f))

  ∘ᵥ-distr-▷ : (f ▷ α) ∘ᵥ (f ▷ β) ≈ f ▷ (α ∘ᵥ β)
  ∘ᵥ-distr-▷ {f = f} = ⟺ (Functor.homomorphism (f ⊚-))

  ρ-∘ᵥ-▷ : unitorˡ.from ∘ᵥ (id₁ ▷ α) ≈ α ∘ᵥ unitorˡ.from
  ρ-∘ᵥ-▷ {α = α} = begin
    unitorˡ.from ∘ᵥ (id₁ ▷ α)    ≈˘⟨ hom.∘-resp-≈ʳ (⊚.F-resp-≈ (id.identity , refl)) ⟩
    unitorˡ.from ∘ᵥ id.F₁ _ ⊚₁ α ≈⟨ unitˡ.⇒.commute (_ , α) ⟩
    α ∘ᵥ unitorˡ.from            ∎

  ▷-∘ᵥ-ρ⁻¹ : (id₁ ▷ α) ∘ᵥ unitorˡ.to ≈ unitorˡ.to ∘ᵥ α
  ▷-∘ᵥ-ρ⁻¹ = conjugate-to (≅.sym unitorˡ) (≅.sym unitorˡ) ρ-∘ᵥ-▷

  λ-∘ᵥ-◁ : unitorʳ.from ∘ᵥ (α ◁ id₁) ≈ α ∘ᵥ unitorʳ.from
  λ-∘ᵥ-◁ {α = α} = begin
    unitorʳ.from ∘ᵥ (α ◁ id₁)      ≈˘⟨ hom.∘-resp-≈ʳ (⊚.F-resp-≈ (refl , id.identity)) ⟩
    unitorʳ.from ∘ᵥ (α ⊚₁ id.F₁ _) ≈⟨ unitʳ.⇒.commute (α , _) ⟩
    α ∘ᵥ unitorʳ.from              ∎

  ◁-∘ᵥ-λ⁻¹ : (α ◁ id₁) ∘ᵥ unitorʳ.to ≈ unitorʳ.to ∘ᵥ α
  ◁-∘ᵥ-λ⁻¹ = conjugate-to (≅.sym unitorʳ) (≅.sym unitorʳ) λ-∘ᵥ-◁

  assoc⁻¹-◁-∘ₕ : associator.to ∘ᵥ (α ◁ (g ∘ₕ f)) ≈ ((α ◁ g) ◁ f) ∘ᵥ associator.to
  assoc⁻¹-◁-∘ₕ {α = α} {g = g} {f = f} = begin
    associator.to ∘ᵥ (α ◁ (g ∘ₕ f))    ≈˘⟨ hom.∘-resp-≈ʳ (⊚.F-resp-≈ (refl , ⊚.identity)) ⟩
    associator.to ∘ᵥ (α ⊚₁ id₂ ⊚₁ id₂) ≈⟨ ⊚-assoc.⇐.commute ((α , id₂) , id₂) ⟩
    ((α ◁ g) ◁ f) ∘ᵥ associator.to     ∎

  assoc⁻¹-▷-◁ : associator.to ∘ᵥ (f ▷ (α ◁ g)) ≈ ((f ▷ α) ◁ g) ∘ᵥ associator.to
  assoc⁻¹-▷-◁ {f = f} {α = α} {g = g} = ⊚-assoc.⇐.commute ((id₂ , α) , id₂)

  assoc⁻¹-▷-∘ₕ : associator.to ∘ᵥ (g ▷ (f ▷ α)) ≈ ((g ∘ₕ f) ▷ α) ∘ᵥ associator.to
  assoc⁻¹-▷-∘ₕ {g = g} {f = f} {α = α} = begin
    associator.to ∘ᵥ (g ▷ (f ▷ α))       ≈⟨ ⊚-assoc.⇐.commute ((id₂ , id₂) , α) ⟩
    ((id₂ ⊚₁ id₂) ⊚₁ α) ∘ᵥ associator.to ≈⟨ hom.∘-resp-≈ˡ (⊚.F-resp-≈ (⊚.identity , refl)) ⟩
    ((g ∘ₕ f) ▷ α) ∘ᵥ associator.to      ∎

  ◁-▷-exchg : ∀ {α : f ⇒₂ g} {β : h ⇒₂ i} → (i ▷ α) ∘ᵥ (β ◁ f) ≈ (β ◁ g) ∘ᵥ (h ▷ α)
  ◁-▷-exchg = [ ⊚ ]-commute
