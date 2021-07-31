{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Cartesian using (Cartesian; module CartesianMonoidal)

-- Defines the following properties of a Category:
-- Cartesian.SymmetricMonoidal
--    a Cartesian category is Symmetric Monoidal if its induced monoidal structure is symmetric

module Categories.Category.Cartesian.SymmetricMonoidal {o ℓ e} (𝒞 : Category o ℓ e) (cartesian : Cartesian 𝒞) where

-- open import Level hiding (suc)
-- open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)

open Category 𝒞
open Commutation 𝒞
open HomReasoning

open import Categories.Category.BinaryProducts 𝒞 using (BinaryProducts; module BinaryProducts)
open import Categories.Object.Terminal 𝒞 using (Terminal)
open import Categories.Object.Product.Core 𝒞 using (module Product)
open import Categories.Morphism 𝒞 using (_≅_; module ≅)
open import Categories.Morphism.Reasoning 𝒞 using (cancelˡ; pullʳ; pullˡ)
open import Categories.Category.Monoidal using (Monoidal)
import Categories.Category.Monoidal.Symmetric as Sym

open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

private
  variable
    W X Y Z : Obj

open Cartesian cartesian using (products; π₁; π₂; ⟨_,_⟩)
open CartesianMonoidal 𝒞 cartesian using (monoidal)
open Sym monoidal using (Symmetric; symmetricHelper)
open Monoidal monoidal using (_⊗₀_; _⊗₁_; module associator)
open BinaryProducts products hiding (⟨_,_⟩; π₁; π₂)

private
  B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
  B = swap

hexagon : [ (X ⊗₀ Y) ⊗₀ Z ⇒ Y ⊗₀ Z ⊗₀ X ]⟨
            B  ⊗₁ id                    ⇒⟨ (Y ⊗₀ X) ⊗₀ Z ⟩
            associator.from             ⇒⟨ Y ⊗₀ X ⊗₀ Z ⟩
            id ⊗₁ B
          ≈ associator.from             ⇒⟨ X ⊗₀ Y ⊗₀ Z ⟩
            B                           ⇒⟨ (Y ⊗₀ Z) ⊗₀ X ⟩
            associator.from
          ⟩
hexagon = begin
      id ⊗₁ swap ∘ assocˡ ∘ swap ⊗₁ id                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
      id ⊗₁ swap ∘ assocˡ ∘ ⟨ ⟨ π₂ ∘ π₁ , π₁ ∘ π₁ ⟩ , id ∘ π₂ ⟩ ≈⟨ refl⟩∘⟨ assocˡ∘⟨⟩ ⟩
      id ⊗₁ swap ∘ ⟨ π₂ ∘ π₁ , ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩ ⟩          ≈⟨ ⁂∘⟨⟩ ⟩
      ⟨ id ∘ π₂ ∘ π₁ , swap ∘ ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩ ⟩           ≈⟨ ⟨⟩-cong₂ identityˡ swap∘⟨⟩ ⟩
      ⟨ π₂ ∘ π₁ , ⟨ id ∘ π₂ , π₁ ∘ π₁ ⟩ ⟩                       ≈⟨ ⟨⟩-congˡ (⟨⟩-congʳ identityˡ) ⟩
      ⟨ π₂ ∘ π₁ , ⟨ π₂ , π₁ ∘ π₁ ⟩ ⟩                            ≈˘⟨ assocˡ∘⟨⟩ ⟩
      assocˡ ∘ ⟨ ⟨ π₂ ∘ π₁ , π₂ ⟩ , π₁ ∘ π₁ ⟩                   ≈˘⟨ refl⟩∘⟨ swap∘⟨⟩ ⟩
      assocˡ ∘ swap ∘ assocˡ                                    ∎

symmetric : Symmetric
symmetric = symmetricHelper record
  { braiding    = record
    { F⇒G = ntHelper record
      { η       = λ _ → swap
      ; commute = λ _ → swap∘⁂
      }
    ; F⇐G = ntHelper record
      { η       = λ _ → swap
      ; commute = λ _ → swap∘⁂
      }
    ; iso = λ _ → record
      { isoˡ = swap∘swap
      ; isoʳ = swap∘swap
      }
    }
  ; commutative = swap∘swap
  ; hexagon     = hexagon
  }
