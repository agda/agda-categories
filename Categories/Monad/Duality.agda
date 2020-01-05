{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Monad.Duality {o ℓ e} (C : Category o ℓ e) where

open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Monad
open import Categories.Comonad

private
  module C = Category C
  open C
  open HomReasoning

coMonad⇒Comonad : Monad C.op → Comonad C
coMonad⇒Comonad M = record
    { F         = Functor.op F
    ; ε         = NaturalTransformation.op η
    ; δ         = NaturalTransformation.op μ
    ; assoc     = M.sym-assoc
    ; sym-assoc = M.assoc
    ; identityˡ = M.identityˡ
    ; identityʳ = M.identityʳ
    }
  where module M = Monad M
        open M using (F; η; μ)

Comonad⇒coMonad : Comonad C → Monad C.op
Comonad⇒coMonad M = record
    { F         = Functor.op F
    ; η         = NaturalTransformation.op ε
    ; μ         = NaturalTransformation.op δ
    ; assoc     = M.sym-assoc
    ; sym-assoc = M.assoc
    ; identityˡ = M.identityˡ
    ; identityʳ = M.identityʳ
    }
  where module M = Comonad M
        open M using (F; ε; δ)
