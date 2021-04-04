open import Algebra.Bundles using (Monoid)

module Categories.Category.Construction.MonoidAsCategory o {c ℓ} (M : Monoid c ℓ) where

open import Data.Unit.Polymorphic
open import Level

open import Categories.Category.Core

open Monoid M

-- A monoid is a category with one object
MonoidAsCategory : Category o c ℓ
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
