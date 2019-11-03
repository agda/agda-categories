{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.CartesianClosed.Locally

module Categories.Category.CartesianClosed.Locally.Properties {o ℓ e} {C : Category o ℓ e}
  (LCCC : Locally C) where

open import Categories.Category.CartesianClosed
open import Categories.Category.Slice
open import Categories.Category.Slice.Properties
open import Categories.Functor
open import Categories.Functor.Slice

private
  module C = Category C
  open C
  open Locally LCCC
  variable
    A B : Obj
            
module _ (f : A ⇒ B) where
  open CartesianClosed (sliceCCC B)

  private
    C/A   = Slice C A
    C/B   = Slice C B
    C/B/f = Slice C/B (sliceobj f)

    fObj : SliceObj C B
    fObj = sliceobj f

    i : Slice⇒ C ⊤ (fObj ^ fObj)
    i = λg π₂

    J : Functor C/A C/B/f
    J = slice⇒slice-slice C f

    I : Functor (Slice C/B (fObj ^ fObj)) C/B
    I = pullback-functorial C/B slice-pullbacks i

    K : Functor C/B/f (Slice C/B (fObj ^ fObj))
    K = Base-F C/B (fObj ⇨-)

  -- this functor should be the right adjoint functor of (BaseChange* C pullbacks f).
  BaseChange⁎ : Functor C/A C/B
  BaseChange⁎ = I ∘F K ∘F J
