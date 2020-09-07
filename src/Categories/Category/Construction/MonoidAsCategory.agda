open import Algebra.Bundles using (Monoid)

module Categories.Category.Construction.MonoidAsCategory {c ℓ} (M : Monoid c ℓ) where

open import Data.Unit
open import Level

open import Categories.Category.Core

open Monoid M

-- A monoid is a category with one object
MonoidAsCategory : Category zero c ℓ
MonoidAsCategory = record
  { Obj = ⊤
  ; assoc = assoc _ _ _
  ; sym-assoc = sym (assoc _ _ _)
  ; identityˡ = identityˡ _
  ; identityʳ = identityʳ _
  ; identity² = identityˡ _
  ; equiv = isEquivalence
  ; ∘-resp-≈ = ∙-cong
  }
