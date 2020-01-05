{-# OPTIONS --without-K --safe #-}

-- 'Traditionally', meaning in nLab and in
-- "Lectures on n-Categories and Cohomology" by Baez and Shulman
-- https://arxiv.org/abs/math/0608420
-- (-2)-Categories are defined to be just a single value, with trivial Hom

-- But that's hardly a definition of a class of things, it's a definition of
-- a single structure!  What we want is the definition of a class which turns
-- out to be (essentially) unique. Rather like the reals are (essentially) the
-- only ordered complete archimedean field.

-- So we will take a -2-Category to be a full-fledge Category, but where
-- 1. |Obj| is (Categorically) contractible
-- 2. |Hom| is connected (all arrows are equal)
-- Note that we don't need to say anything at all about ≈

module Categories.Minus2-Category where

open import Level
open import Categories.Category
open import Data.Product using (Σ)
import Categories.Morphism as M

private
  variable
    o ℓ e : Level

record -2-Category : Set (suc (o ⊔ ℓ ⊔ e)) where
   field
     cat : Category o ℓ e
   open Category cat public
   open M cat using (_≅_)

   field
     Obj-Contr : Σ Obj (λ x → (y : Obj) → x ≅ y)
     Hom-Conn  : {x y : Obj} {f g : x ⇒ y} → f ≈ g
