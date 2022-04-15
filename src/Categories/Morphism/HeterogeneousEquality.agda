{-# OPTIONS --without-K --safe #-}
open import Categories.Category using (Category; module Definitions)

module Categories.Morphism.HeterogeneousEquality where

open import Level

open import Categories.Category using (_[_,_]; _[_≈_])
open import Categories.Morphism using (_≅_)
open import Categories.Morphism.Notation using (_[_≅_])

private
  variable
    o ℓ e : Level


Along_,_[_≈_] : {C : Category o ℓ e}{A A' B B' : Category.Obj C}
              → (i : C [ A ≅ A' ])(j : C [ B ≅ B' ])(f : C [ A , B ])(f' : C [ A' , B' ]) → Set e
Along_,_[_≈_] {C = C} i j f f' = C [ _≅_.from j ∘ f ≈ f' ∘ _≅_.from i ]
  where open Category C
