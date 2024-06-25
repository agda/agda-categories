{-# OPTIONS --without-K --safe #-}
open import Data.Product using (_,_; _×_; map; zip)
open import Function.Base using (_$_; flip)
open import Level
open import Relation.Binary.Core using (Rel)

open import Categories.Category using (Category; module Definitions)
open import Categories.Category.Product renaming (Product to _×ᶜ_)
open import Categories.Functor

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

-- Definition of the "Twisted Arrow" Category of a Category 𝒞
module Categories.Category.Construction.TwistedArrow {o ℓ e} (𝒞 : Category o ℓ e) where

private
  open module 𝒞 = Category 𝒞


open M 𝒞
open Definitions 𝒞
open MR 𝒞
open HomReasoning

private
  variable
    A B C : Obj

record Morphism : Set (o ⊔ ℓ) where
  field
    {dom} : Obj
    {cod} : Obj
    arr   : dom ⇒ cod

record Morphism⇒ (f g : Morphism) : Set (ℓ ⊔ e) where
  constructor mor⇒
  private
    module f = Morphism f
    module g = Morphism g

  field
    {dom⇐} : g.dom ⇒ f.dom
    {cod⇒} : f.cod ⇒ g.cod
    square : cod⇒ ∘ f.arr ∘ dom⇐ ≈ g.arr

TwistedArrow : Category (o ⊔ ℓ) (ℓ ⊔ e) e
TwistedArrow = record
  { Obj       = Morphism
  ; _⇒_       = Morphism⇒
  ; _≈_       = λ f g → dom⇐ f ≈ dom⇐ g × cod⇒ f ≈ cod⇒ g
  ; id        = mor⇒ (identityˡ ○ identityʳ)
  ; _∘_       = λ {A} {B} {C} m₁ m₂ → mor⇒ {A} {C} (∘′ m₁ m₂  ○ square m₁)
  ; assoc     = sym-assoc , assoc
  ; sym-assoc = assoc , sym-assoc
  ; identityˡ = identityʳ , identityˡ
  ; identityʳ = identityˡ , identityʳ
  ; identity² = identity² , identity²
  ; equiv     = record
    { refl  = refl , refl
    ; sym   = map sym sym
    ; trans = zip trans trans
    }
  ; ∘-resp-≈  = zip (flip ∘-resp-≈) ∘-resp-≈
  }
  where
  open Morphism⇒
  open Equiv
  open HomReasoning
  ∘′ : ∀ {A B C} (m₁ : Morphism⇒ B C) (m₂ : Morphism⇒ A B) →
    (cod⇒ m₁ ∘ cod⇒ m₂) ∘ Morphism.arr A ∘ (dom⇐ m₂ ∘ dom⇐ m₁) ≈ cod⇒ m₁ ∘ Morphism.arr B ∘ dom⇐ m₁
  ∘′ {A} {B} {C} m₁ m₂ = begin
    (cod⇒ m₁ ∘ cod⇒ m₂) ∘ Morphism.arr A ∘ (dom⇐ m₂ ∘ dom⇐ m₁) ≈⟨ pullʳ sym-assoc ⟩
    cod⇒ m₁ ∘ (cod⇒ m₂ ∘ Morphism.arr A) ∘ (dom⇐ m₂ ∘ dom⇐ m₁) ≈⟨ refl⟩∘⟨ (pullˡ assoc) ⟩
    cod⇒ m₁ ∘ (cod⇒ m₂ ∘ Morphism.arr A ∘ dom⇐ m₂) ∘ dom⇐ m₁   ≈⟨ (refl⟩∘⟨ square m₂ ⟩∘⟨refl) ⟩
    cod⇒ m₁ ∘ Morphism.arr B ∘ dom⇐ m₁ ∎


-- Consider TwistedArrow as the comma category * / Hom[C][-,-]
-- We have the codomain functor TwistedArrow → C.op × C

module _ where
  open Morphism
  open Morphism⇒
  open Functor
  Forget : Functor TwistedArrow (𝒞.op ×ᶜ 𝒞)
  Forget .F₀ x = dom x , cod x
  Forget .F₁ f = dom⇐ f , cod⇒ f
  Forget .identity = Equiv.refl , Equiv.refl
  Forget .homomorphism = Equiv.refl , Equiv.refl
  Forget .F-resp-≈ e = e
