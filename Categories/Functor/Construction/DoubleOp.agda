{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Construction.DoubleOp {o ℓ e} {C : Category o ℓ e} where

open Category C
open Equiv

open import Function renaming (id to idFun)

open import Categories.Functor

opopC⇒C : Functor (Category.op op) C
opopC⇒C = record
  { F₀           = idFun
  ; F₁           = idFun
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = idFun
  }

C⇒opopC : Functor C (Category.op op)
C⇒opopC = record
  { F₀           = idFun
  ; F₁           = idFun
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = idFun
  }
