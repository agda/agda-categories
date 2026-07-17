{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Cartesian using (Cartesian)

-- Defines the following properties of a Category:
-- Cartesian.SymmetricMonoidal
--    a Cartesian category is Symmetric Monoidal

module Categories.Category.Cartesian.SymmetricMonoidal {o ℓ e} (𝒞 : Category o ℓ e) (cartesian : Cartesian 𝒞) where

open Category 𝒞
open Commutation 𝒞
open HomReasoning

open import Categories.Category.BinaryProducts 𝒞 using (module BinaryProducts)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Monoidal using (Monoidal)
import Categories.Category.Monoidal.Symmetric as Sym

open import Categories.NaturalTransformation using (ntHelper)

private
  variable
    W X Y Z : Obj

open Cartesian cartesian using (π₁; π₂; ⟨_,_⟩; ⟨⟩-congʳ; ⟨⟩-congˡ; ⟨⟩-cong₂; 
  swap; swap∘⟨⟩; swap∘swap; assocˡ; assocˡ∘⟨⟩; ×₁∘⟨⟩; ⟨⟩∘; swap∘×₁)
open CartesianMonoidal cartesian using (monoidal)
open Sym monoidal using (Symmetric; symmetricHelper)
open Monoidal monoidal using (_⊗₀_; _⊗₁_; module associator)

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
      id ⊗₁ swap ∘ assocˡ ∘ swap ⊗₁ id                          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
      id ⊗₁ swap ∘ assocˡ ∘ ⟨ ⟨ π₂ ∘ π₁ , π₁ ∘ π₁ ⟩ , id ∘ π₂ ⟩ ≈⟨ refl⟩∘⟨ assocˡ∘⟨⟩ ⟩
      id ⊗₁ swap ∘ ⟨ π₂ ∘ π₁ , ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩ ⟩          ≈⟨ ×₁∘⟨⟩ ⟩
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
      ; commute = λ _ → swap∘×₁
      }
    ; F⇐G = ntHelper record
      { η       = λ _ → swap
      ; commute = λ _ → swap∘×₁
      }
    ; iso = λ _ → record
      { isoˡ = swap∘swap
      ; isoʳ = swap∘swap
      }
    }
  ; commutative = swap∘swap
  ; hexagon     = hexagon
  }
