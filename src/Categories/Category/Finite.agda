{-# OPTIONS --without-K --safe #-}

module Categories.Category.Finite where

open import Level

open import Categories.Adjoint.Equivalence
open import Categories.Category.Core
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

  --
  --   /------------\
  --  <      -       \
  -- C       |        S
  --  \      -       ^
  --   \------------/
  --
  field
    ⊣equiv : ⊣Equivalence shapeCat C

  module ⊣equiv = ⊣Equivalence ⊣equiv
  open ⊣equiv public
