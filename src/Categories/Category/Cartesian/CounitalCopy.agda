{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Cartesian using (Cartesian)

-- Defines the following properties of a Category:
-- Cartesian.CounitalCopy
--    a Cartesian category is a counital copy category
--
-- Counital copy categories are the gs-monoidal ones whose comultiplication is
-- natural, so this is Cartesian.GSMonoidal plus that one law, and the law is
-- two rewrites already in Categories.Category.BinaryProducts.  The counit is
-- natural as well, by !-unique₂, and that is the remaining step from counital
-- copy back to cartesian.

module Categories.Category.Cartesian.CounitalCopy
  {o ℓ e} (𝒞 : Category o ℓ e) (cartesian : Cartesian 𝒞) where

open Category 𝒞
open HomReasoning

open import Categories.Category.Cartesian.GSMonoidal using (gsMonoidal)
open import Categories.Category.Cartesian.SymmetricMonoidal using (symmetric)
open import Categories.Category.Monoidal.CounitalCopy using (CounitalCopy)

private
  variable
    A B : Obj

open Cartesian cartesian using (_×₁_; Δ; Δ∘; ×₁∘Δ)

Δ-natural : (f : A ⇒ B) → Δ ∘ f ≈ (f ×₁ f) ∘ Δ
Δ-natural _ = Δ∘ ○ ⟺ ×₁∘Δ

counitalCopy : CounitalCopy (symmetric 𝒞 cartesian)
counitalCopy = record
  { gsMonoidal = gsMonoidal 𝒞 cartesian
  ; natural    = Δ-natural
  }
