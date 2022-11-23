module Categories.Functor.Construction.LiftAlgebras where

open import Level

open import Categories.Category using (Category)
open import Categories.Functor hiding (id)
open import Categories.Functor.Algebra
open import Categories.Functor.Coalgebra
open import Categories.Functor.Bialgebra using (Distr-law)
open import Categories.NaturalTransformation
open import Categories.Category.Construction.F-Algebras
open import Categories.Functor.Properties
open import Categories.Category

import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

LiftAlgebras : {C : Category o ℓ e} → (T : Endofunctor C) → (F : Endofunctor C) → (Distr-law T F) → Endofunctor (F-Algebras T)
LiftAlgebras {C = C} T F μ = record
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

