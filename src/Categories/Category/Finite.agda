{-# OPTIONS --without-K --safe #-}

module Categories.Category.Finite where

open import Level
open import Data.Nat using (ℕ)
open import Data.Fin

open import Categories.Adjoint.Equivalence
open import Categories.Category
open import Categories.Functor
open import Categories.Category.Finite.Fin

-- definition of a finite category
-- 
-- the idea is to require a functor from C to a category generated from a finite shape
-- is the right adjoint.
--
-- Question: it seems to me right adjoint is enough, though the original plan is to
-- use adjoint equivalence. intuitively, the shape category is an "overapproximation"
-- of C, which is a very strong constraint. so requiring adjoint equivalence sounds an
-- unnecessarily stronger constraint. is adjoint equivalence necessary?
--
-- Answer: probably yes. adjoint equivalence seems necessary as the notion needs to
-- show that shapes are preserved.
--
-- c.f. Categories.Adjoint.Equivalence.Properties.⊣equiv-preserves-diagram
record Finite {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    shape : FinCatShape

  open FinCatShape public renaming (size to ∣Obj∣)

  shapeCat : Category _ _ _
  shapeCat = FinCategory shape

  field
    S⇒C    : Functor shapeCat C
    C⇒S    : Functor C shapeCat
    --
    --   /------------\
    --  <      -       \
    -- C       |        S
    --  \      -       ^
    --   \------------/
    --
    ⊣equiv : ⊣Equivalence S⇒C C⇒S

  module S⇒C    = Functor S⇒C
  module C⇒S    = Functor C⇒S
  module ⊣equiv = ⊣Equivalence ⊣equiv
