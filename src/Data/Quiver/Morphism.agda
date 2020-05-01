{-# OPTIONS --without-K --safe #-}

module Data.Quiver.Morphism where

open import Level
open import Function renaming (id to idFun; _∘_ to _⊚_)
open import Data.Quiver

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

record Morphism (G : Quiver o ℓ e) (G′ : Quiver o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module G  = Quiver G
    module G′ = Quiver G′

  field
    M₀       : G.Obj → G′.Obj
    M₁       : ∀ {A B} → A G.⇒ B → M₀ A G′.⇒ M₀ B
    M-resp-≈ : ∀ {A B} {f g : A G.⇒ B} → f G.≈ g → M₁ f G′.≈ M₁ g

id : {G : Quiver o ℓ e} → Morphism G G
id = record { M₀ = idFun ; M₁ = idFun ; M-resp-≈ = idFun }

_∘_ : {G₁ G₂ G₃ : Quiver o ℓ e} (m₁ : Morphism G₂ G₃) (m₂ : Morphism G₁ G₂) → Morphism G₁ G₃
m₁ ∘ m₂ = record
  { M₀ = M₀ m₁ ⊚ M₀ m₂
  ; M₁ = M₁ m₁ ⊚ M₁ m₂
  ; M-resp-≈ = M-resp-≈ m₁ ⊚ M-resp-≈ m₂
  }
  where open Morphism
