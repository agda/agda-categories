{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Monad.Duality {o ℓ e} (C : Category o ℓ e) where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)
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


module MonadDualityConversionProperties where
  private
    coMonad⇔Comonad : ∀ (coMonad : Monad C.op) →
                    Comonad⇒coMonad (coMonad⇒Comonad coMonad) ≡ coMonad
    coMonad⇔Comonad _ = refl

    Comonad⇔coMonad : ∀ (M : Comonad C) → coMonad⇒Comonad (Comonad⇒coMonad M) ≡ M
    Comonad⇔coMonad _ = refl
