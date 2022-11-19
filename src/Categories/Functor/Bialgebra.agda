{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Bialgebra where

open import Level
open import Categories.Category using (Category)
open import Categories.Functor
open import Categories.Functor.Algebra
open import Categories.Functor.Coalgebra
open import Categories.NaturalTransformation

{-
given two endofunctors T and F on a category C, we can define a (T,F)-bialgebra to be an object of C equipped with the structure of a T-algebra and an F-coalgebra, i.e. just a triple (A,a,c), where a:TA→A and c:A→FA.
μ is a distributive law (of T over F): a natural transformation μ:TF→FT.
A μ-bialgebra is a (T,F)-bialgebra (A,a,c) such that c∘a=Fa∘μ_A∘Tc
[category theory - How are F-bialgebras defined? - Mathematics Stack Exchange](https://math.stackexchange.com/questions/3057781/how-are-f-bialgebras-defined#answer-3057859)
-}

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} where

  module _ (T : Endofunctor C) (F : Endofunctor C) where
    Distr-law : Set (o ⊔ ℓ ⊔ e)
    Distr-law = NaturalTransformation (T ∘F F) (F ∘F T)

  record μ-Bialgebra (T : Endofunctor C) (F : Endofunctor C) (μ : Distr-law T F)
       : Set (o ⊔ ℓ ⊔ e) where
    open Category C
    open Functor
    open NaturalTransformation
    field
      A : Obj
      a₁ : F-Algebra-on T A
      c₁ : F-Coalgebra-on F A
    module F = Functor F
    module T = Functor T
    field
      respects-μ : c₁ ∘ a₁ ≈ ((F.₁) a₁) ∘ (μ .η A) ∘ ((T.₁) c₁)
    --to access the (co)algebras induced by the morphisms:
    a : F-Algebra T
    a = record { A = A ; α = a₁ }

    c : F-Coalgebra F
    c = record { A = A ; α = c₁ }


  open μ-Bialgebra

  record μ-Bialgebra-Morphism {T F : Endofunctor C} {μ : Distr-law T F} (X Y : μ-Bialgebra T F μ) : Set (o ⊔ ℓ ⊔ e) where
    open Category C
    module X = μ-Bialgebra X
    module Y = μ-Bialgebra Y
    open Functor F
    field
      f : X.A ⇒ Y.A
      f-is-alg-morph : is-F-Algebra-Morphism X.a Y.a f
      f-is-coalg-morph : is-F-Coalgebra-Morphism X.c Y.c f
