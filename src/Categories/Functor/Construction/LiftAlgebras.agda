{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.DistributiveLaw using (DistributiveLaw)
module Categories.Functor.Construction.LiftAlgebras {o ℓ e} {C : Category o ℓ e} (T F : Endofunctor C) (μ : DistributiveLaw T F) where

open import Level
open import Function using (_$_)

open import Categories.Functor.Algebra using (F-Algebra;F-Algebra-Morphism)
open import Categories.Functor.Coalgebra using (F-Coalgebra;F-Coalgebra-Morphism)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Category.Construction.F-Algebras using (F-Algebras)
open import Categories.Category.Construction.F-Coalgebras using (F-Coalgebras)
open import Categories.Functor.Properties using ([_]-resp-square)

open import Categories.Object.Initial

import Categories.Morphism.Reasoning as MR

{-
For theoretical background, see header comment in
`Categories.Category.Construction.mu-Bialgebras`
-}

LiftAlgebras : Endofunctor (F-Algebras T)
LiftAlgebras = record
  { F₀           = λ X → record { A = (F .F₀) (X .A);  α = (F₁ F) (X .α) ∘ (μ .η) (X .A) }
  ; F₁           = λ α₁ → record { f = (F .F₁) (α₁ .f) ; commutes = commut α₁ }
  ; identity     = identity F
  ; homomorphism = homomorphism F
  ; F-resp-≈     = F-resp-≈ F
  }
  where
    open Category C
    open Definitions C
    open MR C
    open HomReasoning
    open Equiv
    open Functor
    open NaturalTransformation
    open F-Algebra
    open F-Algebra-Morphism
    commut : { X Y : F-Algebra T } → (a : F-Algebra-Morphism X Y) →
      (F .F₁) (a .f) ∘ ((F .F₁) (X .α) ∘ (μ .η) (X .A)) ≈
      ((F .F₁) (Y .α) ∘ (μ .η) (Y .A)) ∘ (T .F₁) ((F .F₁) (a .f))
    commut {X} {Y} a = ⟺ (glue (⟺ ([ F ]-resp-square (commutes a))) (commute μ (f a)))

liftInitial : Initial (F-Algebras T) → Initial (F-Coalgebras LiftAlgebras)
liftInitial μT = record
  { ⊥ = record
    { A = ⊥
    ; α = ⦅ F₀ ⊥ ⦆
    }
  ; ⊥-is-initial = record
    { ! = λ {A = X} →
      let
        a = F-Coalgebra.A X
        c = F-Coalgebra.α X
      in record
      { f = ⦅ a ⦆
      ; commutes = !-unique₂ (c ∘ ⦅ a ⦆) (F₁ ⦅ a ⦆ ∘ ⦅ F₀ ⊥ ⦆)
      }
    ; !-unique = λ {A = X} g → !-unique (F-Coalgebra-Morphism.f g)
    }
  }
  where
    open Initial μT
    open Category (F-Algebras T)
    open Definitions (F-Algebras T)
    open MR (F-Algebras T)
    open HomReasoning
    open Equiv
    private
      ⦅_⦆ = λ X → ! {A = X} -- "banana brackets" (Meijer 1991)
    open Functor LiftAlgebras
