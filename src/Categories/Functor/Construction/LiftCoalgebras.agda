{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Functor.DistributiveLaw using (DistributiveLaw)
module Categories.Functor.Construction.LiftCoalgebras {o ℓ e} {C : Category o ℓ e} (T F : Endofunctor C) (μ : DistributiveLaw T F) where

open import Level

open import Categories.Functor.Algebra using (F-Algebra;F-Algebra-Morphism)
open import Categories.Functor.Coalgebra using (F-Coalgebra; F-Coalgebra-Morphism)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Category.Construction.F-Coalgebras using (F-Coalgebras)
open import Categories.Category.Construction.F-Algebras using (F-Algebras)
open import Categories.Functor.Construction.LiftAlgebras using (LiftAlgebras)
open import Categories.Functor.Duality using (F-Coalgebra-Morphism⇒coF-Algebra-Morphism)

open import Categories.Object.Terminal

import Categories.Morphism.Reasoning as MR

{-
For theoretical background, see header comment in
`Categories.Category.Construction.mu-Bialgebras`
-}

LiftCoalgebras : Endofunctor (F-Coalgebras F)
LiftCoalgebras = record
  { F₀           = λ X → record { A = (T .F₀) (X .A);  α = (μ .η) (X .A) ∘ (F₁ T) (X .α) }
  ; F₁           = λ α₁ → record
    { f = (T .F₁) (α₁ .f)
    ; commutes = F-Algebra-Morphism.commutes
        (T̂ᵒᵖ.F₁ (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₁))
    }
  ; identity     = identity T
  ; homomorphism = homomorphism T
  ; F-resp-≈     = F-resp-≈ T
  }
  where
    open Category C
    open Functor
    open NaturalTransformation
    open F-Coalgebra
    open F-Coalgebra-Morphism
    private module T̂ᵒᵖ = Functor (LiftAlgebras (Functor.op F) (Functor.op T) (NaturalTransformation.op μ))

liftTerminal : Terminal (F-Coalgebras F) → Terminal (F-Algebras LiftCoalgebras)
liftTerminal νF = record
  { ⊤ = record
    { A = ⊤
    ; α = 〖 F₀ ⊤ 〗
    }
  ; ⊤-is-terminal = record
    { ! = λ {A = X} →
      let
        c = F-Algebra.A X
        a = F-Algebra.α X
      in record
      { f = 〖 c 〗
      ; commutes = !-unique₂ {f = (〖 c 〗 ∘ a)} {g = (〖 F₀ ⊤ 〗 ∘ F₁ 〖 c 〗)}
      }
    ; !-unique = λ {A = X} g → !-unique (F-Algebra-Morphism.f g)
    }
  }
  where
    open Terminal νF
    open Category (F-Coalgebras F)
    open Definitions (F-Coalgebras F)
    open MR (F-Coalgebras F)
    open HomReasoning
    open Equiv
    private
      〖_〗 = λ X → ! {A = X} -- -- "lenses" (Meijer 1991)
    open Functor LiftCoalgebras
