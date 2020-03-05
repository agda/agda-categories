{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal

module Categories.Category.Monoidal.Traced {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open Category C

open import Level

open import Data.Product using (_,_)

open import Categories.Category.Monoidal.Symmetric M

private
  variable
    A B X Y : Obj
    f g : A ⇒ B

------------------------------------------------------------------------------
-- Def from http://ncatlab.org/nlab/show/traced+monoidal+category
-- 
-- A symmetric monoidal category (C,⊗,1,b) (where b is the symmetry) is
-- said to be traced if it is equipped with a natural family of functions
-- 
-- TrXA,B:C(A⊗X,B⊗X)→C(A,B)
-- satisfying three axioms:
-- 
-- Vanishing: Tr1A,B(f)=f (for all f:A→B) and
-- TrX⊗YA,B=TrXA,B(TrYA⊗X,B⊗X(f)) (for all f:A⊗X⊗Y→B⊗X⊗Y)
-- 
-- Superposing: TrXC⊗A,C⊗B(idC⊗f)=idC⊗TrXA,B(f) (for all f:A⊗X→B⊗X)
-- 
-- Yanking: TrXX,X(bX,X)=idX

-- Traced monoidal category
--  is a symmetric monoidal category with a trace operation
-- 
-- note that the definition in this library is significantly easier than the previous one because
-- we adopt a simpler definition of monoidal category to begin with.
record Traced : Set (levelOfTerm M) where
  field
    symmetric : Symmetric

  open Symmetric symmetric public

  field
    trace : ∀ {X A B} → A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B

    vanishing₁  : trace {X = unit} (f ⊗₁ id) ≈ f
    vanishing₂  : trace {X = X} (trace {X = Y} (associator.to ∘ f ∘ associator.from))
                ≈ trace {X = X ⊗₀ Y} f
    superposing : trace {X = X} (associator.to ∘ id {Y} ⊗₁ f ∘ associator.from) ≈ id {Y} ⊗₁ trace {X = X} f
    yanking     : trace (braiding.⇒.η (X , X)) ≈ id
