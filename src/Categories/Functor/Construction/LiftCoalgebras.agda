{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Functor.DistributiveLaw using (DistributiveLaw)
module Categories.Functor.Construction.LiftCoalgebras {o ℓ e} {C : Category o ℓ e} (T F : Endofunctor C) (μ : DistributiveLaw T F) where

open import Level

open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Category.Construction.F-Coalgebras using (F-Coalgebras)
open import Categories.Functor.Construction.LiftAlgebras using (LiftAlgebras)
open import Categories.Functor.Duality

import Categories.Morphism.Reasoning as MR

LiftCoalgebras : Endofunctor (F-Coalgebras F)
LiftCoalgebras = record

  { F₀           = λ X → coF-Algebra⇒F-Coalgebra (F₀ (F-Coalgebra⇒coF-Algebra X))
  ; F₁           = λ α₁ → coF-Algebra-Morphism⇒F-Coalgebra-Morphism (F₁ (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₁))
  ; identity     = Functor.identity T
  ; homomorphism = Functor.homomorphism T
  ; F-resp-≈     = Functor.F-resp-≈ T
  }
  where
    open NaturalTransformation μ renaming (op to μ-op )
    open Functor (LiftAlgebras (Functor.op F) (Functor.op T) μ-op)
