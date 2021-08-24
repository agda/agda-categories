{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.LT-Models where

-- Given a fixed Lawvere Theory LT and a fixed category C,
-- the Functors [LT , C] form a category.

-- The proof is basically the same as that of Functors.

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-CartesianCategory)
open import Categories.NaturalTransformation
  using (NaturalTransformation; _∘ᵥ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
open import Categories.Theory.Lawvere using (LawvereTheory; ModelsOf_In_)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

-- The reason the proofs below are so easy is that _∘ᵥ_ 'computes' all the way down into
-- expressions in C, from which the properties follow.
LT-Models : LawvereTheory ℓ e → CartesianCategory o′ ℓ′ e′ → Category (ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (ℓ ⊔ ℓ′ ⊔ e′) e′
LT-Models LT C = record
  { Obj       = ModelsOf LT In C
  ; _⇒_       = λ m₁ m₂ → NaturalTransformation (ModelsOf_In_.mod m₁) (ModelsOf_In_.mod m₂)
  ; _≈_       = _≃_
  ; id        = idN
  ; _∘_       = _∘ᵥ_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = ≃-isEquivalence
  ; ∘-resp-≈  = λ eq eq′ → ∘-resp-≈ eq eq′
  }
  where
    module C = CartesianCategory C using (U)
    open Category C.U

LT-SetoidsModels : {ℓ′ e′ : Level} → LawvereTheory ℓ e → Category (ℓ ⊔ e ⊔ suc (ℓ′ ⊔ e′)) (ℓ ⊔ ℓ′ ⊔ e′) (ℓ′ ⊔ e′)
LT-SetoidsModels {ℓ′ = ℓ′} {e′} LT = LT-Models LT (Setoids-CartesianCategory ℓ′ e′)
