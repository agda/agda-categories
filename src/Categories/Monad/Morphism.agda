{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Monad using (Monad) renaming (id to idM)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation renaming (id to idN)
open NaturalTransformation

module Categories.Monad.Morphism {o ℓ e} {C : Category o ℓ e} where

module _ {D : Category o ℓ e} where
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


  -- monad 2-cell in the sense of https://ncatlab.org/nlab/show/monad#the_bicategory_of_monads
  record Monad²⇒ {M : Monad C} {N : Monad D} (Γ Δ : Monad⇒ M N) : Set (o ⊔ ℓ ⊔ e) where

    private
      module M = Monad M
      module N = Monad N
      module Γ = Monad⇒ Γ
      module Δ = Monad⇒ Δ
      open module D = Category D using (_∘_; _≈_)

    field
      m : NaturalTransformation Γ.X Δ.X

    module m = NaturalTransformation m


    field
      comm : ∀ {U} → Δ.α.η U ∘ N.F.₁ (m.η U) ≈ m.η (M.F.₀ U) ∘ Γ.α.η U

-- monad morphism in a different sense:
-- monads are on the same category, X is the identity
--
-- Really we would like to view this as a special case of the above, e.g. use a
-- shared record of monad morphism properties containing the natural
-- transformation and laws. However, this is not possible, as the following
-- natural transformation would not be from N.F to M.F, but instead would be
-- composed with the identity functor on both sides.
--
-- Unfortunately these natural transformations are not only not equal, but
-- equality cannot be _stated_ as they are not between definitionally equal
-- functors. Instead it is better to have a special definition with the identity
-- functors removed.
record Monad⇒-id (M N : Monad C) : Set (o ⊔ ℓ ⊔ e) where

  private
    module M = Monad M
    module N = Monad N
    open module C = Category C using (_∘_; _≈_)

  field
    α : NaturalTransformation N.F M.F

  module α = NaturalTransformation α

  field
    unit-comp : ∀ {U} → α.η U ∘ N.η.η U ≈ M.η.η U
    mult-comp : ∀ {U} → α.η U ∘ (N.μ.η U) ≈ M.μ.η U ∘ α.η (M.F.₀ U) ∘ N.F.₁ (α.η U)

module _ {T : Monad C} where
  private
    module T = Monad T
  open Monad⇒-id
  open Category C
  open HomReasoning
  open MR C
  Monad⇒-id-id : (Monad⇒-id T T)
  Monad⇒-id-id .α = idN
  Monad⇒-id-id .unit-comp {_} = identityˡ
  Monad⇒-id-id .mult-comp {U} = begin
      id ∘ T.μ.η U            ≈⟨ id-comm-sym ⟩
      T.μ.η U ∘ id            ≈⟨ refl⟩∘⟨ introʳ T.F.identity ⟩
      T.μ.η U ∘ id ∘ T.F.₁ id ∎

module _ {S R T : Monad C} where
  private
    module S = Monad S
    module T = Monad T
    module R = Monad R
    module C = Category C
  open Monad⇒-id
  open C using(_∘_; _≈_)
  open MR C
  open C.HomReasoning
  open Monad

  Monad⇒-id-∘ : (Monad⇒-id T R) → (Monad⇒-id S T) → (Monad⇒-id S R)
  Monad⇒-id-∘ σ τ .α = τ .α ∘ᵥ σ .α
  Monad⇒-id-∘ σ τ .unit-comp {U} = begin
      (τ .α .η U ∘  σ .α .η U) ∘ R .η .η U ≈⟨ pullʳ (σ .unit-comp) ⟩
      τ .α .η U ∘ T .η .η U                ≈⟨ τ .unit-comp ⟩
      S .η .η U                            ∎
  Monad⇒-id-∘ σ τ .mult-comp {U} = begin
      (τ .α .η U ∘ σ .α .η U) ∘ R.μ.η U
        ≈⟨ pullʳ (σ .mult-comp) ⟩
      τ .α .η U ∘ (T.μ.η U ∘ σ .α .η (T.F.₀ U) ∘ R.F.₁ (σ .α .η U))
        ≈⟨ pullˡ (τ .mult-comp) ⟩
      (S.μ.η U ∘ τ .α.η (S.F.₀ U) ∘ T.F.₁ (τ .α.η U)) ∘ σ .α.η (T.F.₀ U) ∘ R.F.₁ (σ .α.η U)
        -- (a ∘ (b ∘ c)) ∘ d ≈ (a ∘ b) ∘ (c ∘ d)
        ≈⟨ pushˡ C.sym-assoc  ⟩
      (S.μ.η U ∘ τ .α.η (S.F.₀ U)) ∘ T.F.₁ (τ .α.η U) ∘ σ .α.η (T.F.₀ U) ∘ R.F.₁ (σ .α.η U)
        ≈⟨ refl⟩∘⟨ extendʳ (σ .α .sym-commute (τ .α.η U)) ⟩
      (S.μ.η U ∘ τ .α.η (S.F.₀ U)) ∘ σ .α.η (S.F.₀ U) ∘ R.F.₁ (τ .α.η U) ∘ R.F.₁ (σ .α.η U)
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ R.F.homomorphism ⟩
      (S.μ.η U ∘ τ .α.η (S.F.₀ U)) ∘ σ .α.η (S.F.₀ U) ∘ R.F.₁ (τ .α.η U ∘ σ .α.η U)
        ≈⟨ assoc²γδ ⟩
      S.μ.η U ∘ (τ .α.η (S.F.₀ U) ∘ σ .α.η (S.F.₀ U)) ∘ R.F.₁ (τ .α.η U ∘ σ .α.η U)
        ∎
