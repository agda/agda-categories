{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Experiments.Additive {o ℓ e} (𝒞 : Category o ℓ e) where

open import Data.Nat
open import Data.Fin
open import Data.Vec

open import Categories.Category.Additive 𝒞
-- open import Categories.Object.Biproduct.Indexed 𝒞

-- open Category 𝒞
-- open HomReasoning
-- open Equiv


-- module _ {j k} {J : Set j} {K : Set k} {P : J → Obj} {Q : K → Obj} (A : IndexedBiproductOf P) (B : IndexedBiproductOf Q) where
--   private
--     module A = IndexedBiproductOf A
--     module B = IndexedBiproductOf B

--   decompose : (A.X ⇒ B.X) → (∀ (j : J) → (k : K) → P j ⇒ Q k)
--   decompose f j k = B.π k ∘ f ∘ A.i j

--   collect : (∀ (j : J) → (k : K) → P j ⇒ Q k) → (A.X ⇒ B.X)
--   collect f[_,_] = A.[ (λ j → B.⟨ (λ k → f[ j , k ]) ⟩) ]

--   -- collect∘decompose : ∀ {f : A.X ⇒ B.X} → collect (decompose f) ≈ f
--   -- collect∘decompose {f = f} = B.⟨⟩-unique _ _ λ k → ⟺ (A.[]-unique _ _ λ j → assoc)

--   -- pointwise : ∀ {f g : A.X ⇒ B.X} → (∀ (j : J) → (k : K) → B.π k ∘ f ∘ A.i j ≈ B.π k ∘ g ∘ A.i j) → f ≈ g
--   -- pointwise {f = f} {g = g} pointwise-eq = begin
--   --   f                                             ≈˘⟨ collect∘decompose ⟩
--   --   B.⟨ (λ k → A.[ (λ j → B.π k ∘ f ∘ A.i j) ]) ⟩ ≈⟨ B.⟨⟩-unique g _ (λ k → ⟺ (A.[]-unique _ _ (λ j → assoc ○ ⟺ (pointwise-eq j k)))) ⟩
--   --   g                                             ∎
