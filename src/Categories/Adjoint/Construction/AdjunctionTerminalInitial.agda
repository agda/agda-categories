{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category
open import Categories.Monad

module Categories.Adjoint.Construction.AdjunctionTerminalInitial {o ℓ e} {C : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e} (M : Monad C) where

open Category C

open import Categories.Adjoint
open import Categories.Functor
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Morphism.Reasoning as MR

open import Categories.Adjoint.Construction.Adjunctions M
open import Categories.Object.Terminal (Split M)
open import Categories.Object.Initial (Split M)
open import Categories.Category.Construction.EilenbergMoore
open import Categories.Category.Construction.Kleisli
open import Categories.Adjoint.Construction.Kleisli M as KL
open import Categories.Adjoint.Construction.EilenbergMoore M as EM


EM-object : SplitObj
EM-object = record
  { D = {!  !}
  ; F = {!   !}
  ; G = {!   !}
  ; adj = {!   !}
  ; eqM = {!   !}
  }

EM-terminal : IsTerminal EM-object
EM-terminal = {!   !}


Kl-object : SplitObj
Kl-object = record
  { D = Kleisli M
  ; F = KL.Free
  ; G = KL.Forgetful
  ; adj = KL.Free⊣Forgetful
  ; eqM = KL.FF≃F
  }

Kl-initial : IsInitial Kl-object
Kl-initial = record
  { ! = {!   !}
  ; !-unique = {!   !}
  }