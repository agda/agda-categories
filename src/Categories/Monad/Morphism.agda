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

  private
    module M = Monad M
    module N = Monad N

  open module D = Category D using (_∘_; _≈_)

  field
    X : Functor C D
    α : NaturalTransformation (N.F ∘F X) (X ∘F M.F)

  module X = Functor X
  module α = NaturalTransformation α

  field
    unit-comp : ∀ {U} → α.η U ∘ (N.η.η (X.₀ U)) ≈ X.₁ (M.η.η U)
    mult-comp : ∀ {U} → α.η U ∘ (N.μ.η (X.₀ U)) ≈ X.₁ (M.μ.η U) ∘ α.η (M.F.₀ U) ∘ N.F.₁ (α.η U)

-- monad morphism in a different sense:
-- monads are on the same category, X is the identity
record Monad⇒-id (M N : Monad C) : Set (o ⊔ ℓ ⊔ e) where

  private
    module M = Monad M
    module N = Monad N

  field
    α : NaturalTransformation N.F M.F

  module α = NaturalTransformation α

  open module C = Category C using (_∘_; _≈_)

  field
    unit-comp : ∀ {U} → α.η U ∘ N.η.η U ≈ M.η.η U
    mult-comp : ∀ {U} → α.η U ∘ (N.μ.η U) ≈ M.μ.η U ∘ α.η (M.F.₀ U) ∘ N.F.₁ (α.η U)

-- monad 2-cell in the sense of https://ncatlab.org/nlab/show/monad#the_bicategory_of_monads
record Monad²⇒ {M : Monad C} {N : Monad D} (Γ Δ : Monad⇒ M N) : Set (o ⊔ ℓ ⊔ e) where

  private
    module M = Monad M
    module N = Monad N
    module Γ = Monad⇒ Γ
    module Δ = Monad⇒ Δ

  field
    m : NaturalTransformation Γ.X Δ.X

  module m = NaturalTransformation m

  open module D = Category D using (_∘_; _≈_)

  field
    comm : ∀ {U} → Δ.α.η U ∘ N.F.₁ (m.η U) ≈ m.η (M.F.₀ U) ∘ Γ.α.η U