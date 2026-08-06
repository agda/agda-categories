{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.GSMonoidal using (GSMonoidal)


-- Counital copy categories as described by Cockett & Lack in "Restriction categories III"
--
-- These are the gs-monoidal categories whose comultiplication is natural.

module Categories.Category.Monoidal.CounitalCopy where
  record CounitalCopy {o ℓ e} {𝒞 : Category o ℓ e} {monoidal : Monoidal 𝒞} (symmetric : Symmetric monoidal) : Set (suc (o ⊔ ℓ ⊔ e)) where
    open Category 𝒞
    open Symmetric symmetric

    field
      gsMonoidal : GSMonoidal symmetric

    open GSMonoidal gsMonoidal public

    field
      natural : ∀ {A B} (f : A ⇒ B) → Δ ∘ f ≈ (f ⊗₁ f) ∘ Δ
