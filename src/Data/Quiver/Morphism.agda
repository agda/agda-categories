{-# OPTIONS --without-K --safe #-}

module Data.Quiver.Morphism where

open import Level
open import Function using () renaming (id to idFun; _∘_ to _⊚_)
open import Data.Quiver
open import Relation.Binary.PropositionalEquality.Subst.Properties using (module Shorthands)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

infix 4 _≃_

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

-- A Morphism of Quivers. As this is meant to be used as the underlying part of a
-- Category, the fields should be named the same as for Functor.
record Morphism (G : Quiver o ℓ e) (G′ : Quiver o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module G  = Quiver G
    module G′ = Quiver G′

  field
    F₀       : G.Obj → G′.Obj
    F₁       : ∀ {A B} → A G.⇒ B → F₀ A G′.⇒ F₀ B
    F-resp-≈ : ∀ {A B} {f g : A G.⇒ B} → f G.≈ g → F₁ f G′.≈ F₁ g

id : {G : Quiver o ℓ e} → Morphism G G
id = record { F₀ = idFun ; F₁ = idFun ; F-resp-≈ = idFun }

_∘_ : {G₁ G₂ G₃ : Quiver o ℓ e} (m₁ : Morphism G₂ G₃) (m₂ : Morphism G₁ G₂) → Morphism G₁ G₃
m₁ ∘ m₂ = record
  { F₀ = F₀ m₁ ⊚ F₀ m₂
  ; F₁ = F₁ m₁ ⊚ F₁ m₂
  ; F-resp-≈ = F-resp-≈ m₁ ⊚ F-resp-≈ m₂
  }
  where open Morphism

-- Define Morphism equivalence here as well.
-- (Proof that it's an equivalence relation straightforward, but not needed?)
record _≃_ {G : Quiver o ℓ e} {G′ : Quiver o′ ℓ′ e′}
    (M M′ : Morphism G G′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  open Quiver G using (_⇒_)
  open Quiver G′ using (_≈_)
  private
    module M  = Morphism M
    module M′ = Morphism M′
  open Shorthands (Quiver._⇒_ G′)

  -- Pick a presentation of equivalence for graph morphisms that works
  -- well with functor equality.

  field
    F₀≡ : ∀ {X} → M.F₀ X ≡ M′.F₀ X
    F₁≡ : ∀ {A B} {f : A ⇒ B} → M.F₁ f ▸ F₀≡ ≈ F₀≡ ◂ M′.F₁ f
