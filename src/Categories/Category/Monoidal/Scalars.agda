{-# OPTIONS --without-K --safe #-}

-- The scalars of a monoidal category are the endomorphisms of the unit object.
-- They form a monoid under composition, with natural left and right actions on
-- the morphisms of the category. These are in fact natural transformations of
-- the identity functor, but we do not prove that here.
-- See https://ncatlab.org/nlab/show/scalar for this terminology
-- in dagger-, compact-, and closed monoidal categories, where scalars are
-- discussed as the endomorphism ring of the tensor unit. The same page cites
-- Abramsky and Coecke, "A categorical semantics of quantum protocols", §6
-- (LiCS 2004, arXiv:quant-ph/0402130, doi:10.1109/LICS.2004.1319636),
-- where scalars are C(I,I) for the tensor unit I.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Category.Monoidal.Scalars
    {o ℓ e} {𝒞 : Category o ℓ e} (M : Monoidal 𝒞) where

open import Algebra.Bundles using (Monoid)

open import Categories.Morphism.Endomorphism 𝒞 using (End; End-∘-Monoid)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)
import Categories.Category.Monoidal.Properties M as MonoidalProps
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open Monoidal M
open Shorthands
open MonoidalProps.Kelly's

Scalar : Set _
Scalar = End unit

Scalar-Monoid : Monoid _ _
Scalar-Monoid = End-∘-Monoid unit

private
  variable
    A B C : Obj

open Monoid Scalar-Monoid public using () renaming (_∙_ to _·ₛ_; ε to idₛ)

module Action where
  infixl 7 _·ˡ_ _·ʳ_

  _·ˡ_ : Scalar → A ⇒ B → A ⇒ B
  s ·ˡ f = λ⇒ ∘ (s ⊗₁ f) ∘ λ⇐

  _·ʳ_ : A ⇒ B → Scalar → A ⇒ B
  f ·ʳ s = ρ⇒ ∘ (f ⊗₁ s) ∘ ρ⇐

  ·ˡ-resp-≈ : ∀ {s t : Scalar} {f g : A ⇒ B} → s ≈ t → f ≈ g → s ·ˡ f ≈ t ·ˡ g
  ·ˡ-resp-≈ s≈t f≈g = ∘-resp-≈ʳ (∘-resp-≈ˡ (s≈t ⟩⊗⟨ f≈g))

  ·ʳ-resp-≈ : ∀ {s t : Scalar} {f g : A ⇒ B} → f ≈ g → s ≈ t → f ·ʳ s ≈ g ·ʳ t
  ·ʳ-resp-≈ f≈g s≈t = ∘-resp-≈ʳ (∘-resp-≈ˡ (f≈g ⟩⊗⟨ s≈t))

  id-·ˡ : ∀ {f : A ⇒ B} → idₛ ·ˡ f ≈ f
  id-·ˡ {f = f} = begin
    λ⇒ ∘ (idₛ ⊗₁ f) ∘ λ⇐  ≈⟨ pullˡ unitorˡ-commute-from ⟩
    (f ∘ λ⇒) ∘ λ⇐         ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
    f                     ∎

  id-·ʳ : ∀ {f : A ⇒ B} → f ·ʳ idₛ ≈ f
  id-·ʳ {f = f} = begin
    ρ⇒ ∘ (f ⊗₁ idₛ) ∘ ρ⇐  ≈⟨ pullˡ unitorʳ-commute-from ⟩
    (f ∘ ρ⇒) ∘ ρ⇐         ≈⟨ cancelʳ unitorʳ.isoʳ ⟩
    f                     ∎

  ·ˡ-∘ : ∀ {s t : Scalar} {f : B ⇒ C} {g : A ⇒ B} →
    (s ·ₛ t) ·ˡ (f ∘ g) ≈ (s ·ˡ f) ∘ (t ·ˡ g)
  ·ˡ-∘ {s = s} {t} {f} {g} = begin
    λ⇒ ∘ ((s ·ₛ t) ⊗₁ (f ∘ g)) ∘ λ⇐                   ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
    λ⇒ ∘ ((s ⊗₁ f) ∘ (t ⊗₁ g)) ∘ λ⇐                   ≈⟨ refl⟩∘⟨ assoc ⟩
    λ⇒ ∘ ((s ⊗₁ f) ∘ ((t ⊗₁ g) ∘ λ⇐))                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ insertˡ unitorˡ.isoˡ ⟩
    λ⇒ ∘ ((s ⊗₁ f) ∘ (λ⇐ ∘ (λ⇒ ∘ ((t ⊗₁ g) ∘ λ⇐))))   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    λ⇒ ∘ (((s ⊗₁ f) ∘ λ⇐) ∘ (λ⇒ ∘ ((t ⊗₁ g) ∘ λ⇐)))   ≈⟨ sym-assoc ⟩
    (λ⇒ ∘ ((s ⊗₁ f) ∘ λ⇐)) ∘ (λ⇒ ∘ ((t ⊗₁ g) ∘ λ⇐))   ∎

  ·ʳ-∘ : ∀ {s t : Scalar} {f : B ⇒ C} {g : A ⇒ B} →
    (f ∘ g) ·ʳ (s ·ₛ t) ≈ (f ·ʳ s) ∘ (g ·ʳ t)
  ·ʳ-∘ {s = s} {t} {f} {g} = begin
    ρ⇒ ∘ ((f ∘ g) ⊗₁ (s ·ₛ t)) ∘ ρ⇐                   ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
    ρ⇒ ∘ ((f ⊗₁ s) ∘ (g ⊗₁ t)) ∘ ρ⇐                   ≈⟨ refl⟩∘⟨ assoc ⟩
    ρ⇒ ∘ ((f ⊗₁ s) ∘ ((g ⊗₁ t) ∘ ρ⇐))                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ insertˡ unitorʳ.isoˡ ⟩
    ρ⇒ ∘ ((f ⊗₁ s) ∘ (ρ⇐ ∘ (ρ⇒ ∘ ((g ⊗₁ t) ∘ ρ⇐))))   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    ρ⇒ ∘ (((f ⊗₁ s) ∘ ρ⇐) ∘ (ρ⇒ ∘ ((g ⊗₁ t) ∘ ρ⇐)))   ≈⟨ sym-assoc ⟩
    (ρ⇒ ∘ ((f ⊗₁ s) ∘ ρ⇐)) ∘ (ρ⇒ ∘ ((g ⊗₁ t) ∘ ρ⇐))   ∎

  unit-merge : ∀ {f : A ⇒ unit} {g : B ⇒ unit} →
    f ∘ ρ⇒ ∘ (id ⊗₁ g) ≈ λ⇒ ∘ (f ⊗₁ g)
  unit-merge {f = f} {g} = begin
    f ∘ ρ⇒ ∘ (id ⊗₁ g)              ≈⟨ sym-assoc ⟩
    (f ∘ ρ⇒) ∘ (id ⊗₁ g)            ≈˘⟨ unitorʳ-commute-from ⟩∘⟨refl ⟩
    (ρ⇒ ∘ (f ⊗₁ id)) ∘ (id ⊗₁ g)    ≈⟨ assoc ⟩
    ρ⇒ ∘ (f ⊗₁ id) ∘ (id ⊗₁ g)      ≈⟨ refl⟩∘⟨ merge₂ʳ ⟩
    ρ⇒ ∘ (f ⊗₁ (id ∘ g))            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ identityˡ ⟩
    ρ⇒ ∘ (f ⊗₁ g)                   ≈˘⟨ coherence₃ ⟩∘⟨refl ⟩
    λ⇒ ∘ (f ⊗₁ g)                   ∎

open Action public
