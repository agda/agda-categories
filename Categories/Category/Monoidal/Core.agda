{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Category.Monoidal.Core {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism

-- record Monoidal : Set (o ⊔ ℓ ⊔ e) where
--   private module C = Category C
--   open C hiding (id; identityˡ; identityʳ; assoc)

--   field
--     _⊗_  : Bifunctor C C C
--     id : Obj

--   field
--     identityˡ : NaturalIsomorphism id⊗x x
--     identityʳ : NaturalIsomorphism x⊗id x
--     assoc : NaturalIsomorphism [x⊗y]⊗z x⊗[y⊗z]

--   open Coherence identityˡ identityʳ assoc

--   field
--     triangle : TriangleLeftSide ≡ⁿ (TriangleRightSide ∘₁ TriangleTopSide)
--     pentagon : (PentagonNESide ∘₁ PentagonNWSide) ≡ⁿ (PentagonSESide ∘₁ (PentagonSSide ∘₁ PentagonSWSide))
