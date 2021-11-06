{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Monad

module Categories.Monad.Morphism {o ℓ e} {C D : Category o ℓ e} where

open import Categories.NaturalTransformation
open import Categories.Functor

open NaturalTransformation

-- monad morphism in the sense of the nLab
-- https://ncatlab.org/nlab/show/monad#the_bicategory_of_monads
-- between generic monads t : a -> a & s : b -> b
record Monad⇒ (M : Monad C) (N : Monad D) : Set (o ⊔ ℓ ⊔ e) where

  module M = Monad M
  module N = Monad N
  module C = Category C
  module D = Category D

  open D

  field
    X : Functor C D
    α : NaturalTransformation (N.F ∘F X) (X ∘F M.F)

  module X = Functor X
  module α = NaturalTransformation α

  field
    unit-comp : ∀ {U : C.Obj} → α.η U ∘ (N.η.η (X.₀ U)) ≈ X.₁ (M.η.η U)
    mult-comp : ∀ {U : C.Obj} → α.η U ∘ (N.μ.η (X.₀ U)) ≈ X.₁ (M.μ.η U) ∘ α.η (M.F.₀ U) ∘ N.F.₁ (α.η U)

-- monad morphism in a different sense:
-- monads are on the same category, X is the identity
record Monad⇒-id (M N : Monad C) : Set (o ⊔ ℓ ⊔ e) where

  module M = Monad M
  module N = Monad N
  module C = Category C

  open C

  field
    α : NaturalTransformation N.F M.F

  module α = NaturalTransformation α

  field
    unit-comp : ∀ {U : C.Obj} → α.η U ∘ N.η.η U ≈ M.η.η U
    mult-comp : ∀ {U : C.Obj} → α.η U ∘ (N.μ.η U) ≈ M.μ.η U ∘ α.η (M.F.₀ U) ∘ N.F.₁ (α.η U)

record Monad²⇒ {M : Monad C} {N : Monad D} (Γ Δ : Monad⇒ M N) : Set (o ⊔ ℓ ⊔ e) where

  module M = Monad M
  module N = Monad N
  module C = Category C
  module D = Category D
  open D

  module Γ = Monad⇒ Γ
  module Δ = Monad⇒ Δ

  field
    m : NaturalTransformation (Monad⇒.X Γ) (Monad⇒.X Δ)

  module m = NaturalTransformation m

  field
    comm : ∀ {U : C.Obj} → Δ.α.η U ∘ N.F.₁ (m.η U) ≈ m.η (M.F.₀ U) ∘ Γ.α.η U