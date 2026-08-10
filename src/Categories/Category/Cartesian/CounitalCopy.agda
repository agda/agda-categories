{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Cartesian using (Cartesian)

-- Defines the following properties of a Category:
-- Cartesian.CounitalCopy
--    a Cartesian category is a counital copy category
--
-- Counital copy categories are the gs-monoidal ones whose comultiplication is
-- natural, so this is Cartesian.GSMonoidal plus that one law, and the law is
-- two rewrites already in Categories.Category.BinaryProducts.
--
-- Every morphism being deterministic is what counital copy adds to gs-monoidal;
-- every morphism being total is `Cartesian.GSMonoidal.total`.  The two together
-- are the whole distance from gs-monoidal back to cartesian.

module Categories.Category.Cartesian.CounitalCopy
  {o ℓ e} (𝒞 : Category o ℓ e) (cartesian : Cartesian 𝒞) where

open Category 𝒞
open HomReasoning

open import Categories.Category.Cartesian.GSMonoidal using (gsMonoidal)
open import Categories.Category.Cartesian.SymmetricMonoidal using (symmetric)
open import Categories.Category.Monoidal.CounitalCopy using (CounitalCopy)
open import Categories.Category.Monoidal.GSMonoidal using (GSMonoidal)

private
  variable
    A B : Obj

open Cartesian cartesian using (_×₁_; Δ; Δ∘; ×₁∘Δ)
open GSMonoidal (gsMonoidal 𝒞 cartesian) using (Deterministic)

deterministic : (f : A ⇒ B) → Deterministic f
deterministic _ = Δ∘ ○ ⟺ ×₁∘Δ

counitalCopy : CounitalCopy (symmetric 𝒞 cartesian)
counitalCopy = record
  { gsMonoidal = gsMonoidal 𝒞 cartesian
  ; natural    = deterministic
  }
