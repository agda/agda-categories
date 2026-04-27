{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

-- Defines the following properties of a Category:
-- Cocartesian.SymmetricMonoidal
--    a Cocartesian category is Symmetric Monoidal

module Categories.Category.Cocartesian.SymmetricMonoidal {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning

private
  module 𝒞 = Category 𝒞

open import Categories.Category.Cocartesian 𝒞
open import Categories.Category.Cocartesian.Monoidal
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
open import Categories.Category.Monoidal.Symmetric
open import Categories.Morphism 𝒞

module CocartesianSymmetricMonoidal (cocartesian : Cocartesian) where
  open Cocartesian cocartesian
  open CocartesianMonoidal cocartesian
  private
    module op-cartesianSymmetricMonoidal = CSM 𝒞.op Dual.op-cartesian

  +-symmetric : Symmetric +-monoidal
  +-symmetric = record
    { braided     = record
      { braiding = record
        { F⇒G = record
          { η           = λ _ → +-swap
          ; commute     = λ _ → ⟺ +₁∘+-swap
          ; sym-commute = λ _ → +₁∘+-swap
          }
        ; F⇐G = record
          { η           = λ _ → +-swap
          ; commute     = λ _ → ⟺ +₁∘+-swap
          ; sym-commute = λ _ → +₁∘+-swap
          }
        ; iso = λ _ → iso +-comm
        }
      ; hexagon₁ = hexagon₂
      ; hexagon₂ = hexagon₁
      }
    ; commutative = commutative
    }
    where open op-cartesianSymmetricMonoidal
          open _≅_
          open Symmetric symmetric using (commutative; hexagon₁; hexagon₂)

  open Symmetric +-symmetric public