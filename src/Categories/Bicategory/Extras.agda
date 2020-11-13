{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory.Extras where

open import Data.Product using (_,_)

open import Categories.Bicategory using (Bicategory)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (appʳ; appˡ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute; [_]-merge)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.IsoEquiv as IsoEquiv

module Extras {o ℓ e t} (Bicat : Bicategory o ℓ e t) where
  open Bicategory Bicat
  private
    variable
      A B C D : Obj
      f g h i : A ⇒₁ B
      α β γ : f ⇒₂ g

  infixr 7 _∘ᵢ_
  infixr 9 _▷ᵢ_
  infixl 9 _◁ᵢ_

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

  module Shorthands where
    λ⇒ = unitorˡ.from
    λ⇐ = unitorˡ.to

    ρ⇒ = unitorʳ.from
    ρ⇐ = unitorʳ.to

    α⇒ = associator.from
    α⇐ = associator.to
  open Shorthands


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
      open Mor (hom A B) using (_≅_; module ≅) public
      open IsoEquiv (hom A B) using (⌞_⌟; _≃_) public
    open MR′
  idᵢ  = λ {A B f} → ≅.refl {A} {B} {f}
  _∘ᵢ_ = λ {A B f g h} α β → ≅.trans {A} {B} {f} {g} {h} β α

  _⊚ᵢ_ : f ≅ h → g ≅ i → f ⊚₀ g ≅ h ⊚₀ i
  α ⊚ᵢ β = record
    { from = from α ⊚₁ from β
    ; to   = to α ⊚₁ to β
    ; iso  = record
      { isoˡ = [ ⊚ ]-merge (isoˡ α) (isoˡ β) ○ ⊚.identity
      ; isoʳ = [ ⊚ ]-merge (isoʳ α) (isoʳ β) ○ ⊚.identity }
    }
    where open _≅_

  _◁ᵢ_ : {g h : B ⇒₁ C} (α : g ≅ h) (f : A ⇒₁ B) → g ∘ₕ f ≅ h ∘ₕ f
  α ◁ᵢ _ = α ⊚ᵢ idᵢ

  _▷ᵢ_ : {f g : A ⇒₁ B} (h : B ⇒₁ C) (α : f ≅ g) → h ∘ₕ f ≅ h ∘ₕ g
  _ ▷ᵢ α = idᵢ ⊚ᵢ α

  ∘ᵥ-distr-◁ : (α ◁ f) ∘ᵥ (β ◁ f) ≈ (α ∘ᵥ β) ◁ f
  ∘ᵥ-distr-◁ {f = f} = ⟺ (Functor.homomorphism (-⊚ f))

  ∘ᵥ-distr-▷ : (f ▷ α) ∘ᵥ (f ▷ β) ≈ f ▷ (α ∘ᵥ β)
  ∘ᵥ-distr-▷ {f = f} = ⟺ (Functor.homomorphism (f ⊚-))

  ρ-∘ᵥ-▷ : λ⇒ ∘ᵥ (id₁ ▷ α) ≈ α ∘ᵥ λ⇒
  ρ-∘ᵥ-▷ {α = α} = begin
    λ⇒ ∘ᵥ (id₁ ▷ α)    ≈˘⟨ hom.∘-resp-≈ʳ (⊚.F-resp-≈ (id.identity , refl)) ⟩
    λ⇒ ∘ᵥ id.F₁ _ ⊚₁ α ≈⟨ unitˡ.⇒.commute (_ , α) ⟩
    α ∘ᵥ λ⇒            ∎

  ▷-∘ᵥ-ρ⁻¹ : (id₁ ▷ α) ∘ᵥ λ⇐ ≈ λ⇐ ∘ᵥ α
  ▷-∘ᵥ-ρ⁻¹ = conjugate-to (≅.sym unitorˡ) (≅.sym unitorˡ) ρ-∘ᵥ-▷

  λ-∘ᵥ-◁ : ρ⇒ ∘ᵥ (α ◁ id₁) ≈ α ∘ᵥ ρ⇒
  λ-∘ᵥ-◁ {α = α} = begin
    ρ⇒ ∘ᵥ (α ◁ id₁)      ≈˘⟨ hom.∘-resp-≈ʳ (⊚.F-resp-≈ (refl , id.identity)) ⟩
    ρ⇒ ∘ᵥ (α ⊚₁ id.F₁ _) ≈⟨ unitʳ.⇒.commute (α , _) ⟩
    α ∘ᵥ ρ⇒              ∎

  ◁-∘ᵥ-λ⁻¹ : (α ◁ id₁) ∘ᵥ ρ⇐ ≈ ρ⇐ ∘ᵥ α
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

  triangle-iso : {f : A ⇒₁ B} {g : B ⇒₁ C} →
                 (g ▷ᵢ unitorˡ ∘ᵢ associator) ≃ (unitorʳ ◁ᵢ f)
  triangle-iso = ⌞ triangle ⌟

  triangle-inv : {f : A ⇒₁ B} {g : B ⇒₁ C} → α⇐ ∘ᵥ g ▷ λ⇐ ≈ ρ⇐ ◁ f
  triangle-inv = _≃_.to-≈ triangle-iso

  pentagon-iso : ∀ {E} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} {i : D ⇒₁ E} →
                 (i ▷ᵢ associator ∘ᵢ associator ∘ᵢ associator ◁ᵢ f) ≃
                 (associator {f = i} {h} {g ∘ₕ f} ∘ᵢ associator)
  pentagon-iso = ⌞ pentagon ⌟

  pentagon-inv : ∀ {E} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} {i : D ⇒₁ E} →
                 (α⇐ ◁ f ∘ᵥ α⇐) ∘ᵥ i ▷ α⇐ ≈ α⇐ ∘ᵥ α⇐ {f = i} {h} {g ∘ₕ f}
  pentagon-inv = _≃_.to-≈ pentagon-iso
