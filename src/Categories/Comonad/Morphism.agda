{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category using (Category)
open import Categories.Comonad
open import Categories.Functor renaming (id to idF)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation renaming (id to idN)
open NaturalTransformation

module Categories.Comonad.Morphism {o ℓ e} {C : Category o ℓ e} where


module _ {D : Category o ℓ e} where
  -- comonad morphism between generic comonads s : a -> a & t : b -> b
  --
  -- As the natural transformation underlying a monad morphism is contravariant,
  -- we take the natural transformation underlying a comonad morphism to be
  -- covariant by symmetry.
  record Comonad⇒ (S : Comonad C) (T : Comonad D) : Set (o ⊔ ℓ ⊔ e) where

    private
      module S = Comonad S
      module T = Comonad T
      open module D = Category D using (_∘_; _≈_)

    field
      X : Functor C D
      α : NaturalTransformation (T.F ∘F X) (X ∘F S.F)

    module X = Functor X
    module α = NaturalTransformation α

    field
      -- we want this but no definitional functionality means sadness
      -- counit-comp : (X ∘ˡ S.ε) ∘ᵥ α ≃ T.ε ∘ʳ X
      counit-comp : ∀ {U} → X.₁ (S.ε.η U) ∘ α.η U ≈ T.ε.η (X.₀ U)
      -- likewise here we want
      -- comult-comp : (X ∘ˡ S.δ) ∘ α ≃ (α ∘ʳ S) ∘ (T ∘ˡ α) ∘ T.δ
      comult-comp : ∀ {U} → X.₁ (S.δ.η U) ∘ α.η U ≈ α.η (S.F.₀ U) ∘ T.F.₁ (α.η U) ∘ T.δ.η (X.₀ U)

  -- not sure if this definition makes sense? or if it should be turned backwards
  record Comonad²⇒ {S : Comonad C} {T : Comonad D} (Γ Δ : Comonad⇒ S T) : Set (o ⊔ ℓ ⊔ e) where

    private
      module S = Comonad S
      module T = Comonad T
      module Γ = Comonad⇒ Γ
      module Δ = Comonad⇒ Δ
      open module D = Category D using (_∘_; _≈_)

    field
      m : NaturalTransformation Γ.X Δ.X

    module m = NaturalTransformation m

    field
      comm : ∀ {U} → Δ.α.η U ∘ T.F.₁ (m.η U) ≈ m.η (S.F.₀ U) ∘ Γ.α.η U

-- comonad morphism in a different sense:
-- comonads are on the same category, X is the identity
record Comonad⇒-id (T S : Comonad C) : Set (o ⊔ ℓ ⊔ e) where

  private
    module T = Comonad T
    module S = Comonad S
    open module C = Category C using (_∘_; _≈_)

  field
    α : NaturalTransformation T.F S.F

  module α = NaturalTransformation α

  field
    counit-comp : ∀ {U} → S.ε.η U ∘ α.η U ≈ T.ε.η U
    comult-comp : ∀ {U} → S.δ.η U ∘ α.η U ≈ α.η (S.F.₀ U) ∘ T.F.₁ (α.η U) ∘ T.δ.η U

module _ {T : Comonad C} where
  private
    module T = Comonad T
  open Comonad⇒-id
  open Category C
  open HomReasoning
  Comonad⇒-id-id : (Comonad⇒-id T T)
  Comonad⇒-id-id .α = idN
  Comonad⇒-id-id .counit-comp {_} = identityʳ
  Comonad⇒-id-id .comult-comp {U} = begin
    T.δ.η U ∘ id
    ≈⟨ identityʳ
     ○ ⟺ identityˡ
     ○ refl⟩∘⟨ ⟺ identityˡ
     ○ refl⟩∘⟨ ⟺ T.F.identity ⟩∘⟨refl
     ⟩
    id ∘ T.F.F₁ id ∘ T.δ.η U
    ∎

module _ {S R T : Comonad C} where
  private
    module S = Comonad S
    module T = Comonad T
    module R = Comonad R
  open Comonad⇒-id
  module C = Category C
  open C using(_∘_; _≈_)
  open MR C
  open C.HomReasoning
  open Comonad

  open import Categories.Tactic.Category using (solve)

  Comonad⇒-id-∘ : (Comonad⇒-id S T) → (Comonad⇒-id T R) → (Comonad⇒-id S R)
  Comonad⇒-id-∘ τ σ .α = σ .α ∘ᵥ τ .α
  Comonad⇒-id-∘ τ σ .counit-comp {U} = begin
    R.ε.η U ∘ (σ .α ∘ᵥ τ .α) .η  U
    ≈⟨ C.sym-assoc ⟩
    (R.ε.η U ∘ σ .α.η U) ∘ τ .α.η  U
    ≈⟨ σ .counit-comp ⟩∘⟨refl ⟩
    T.ε.η U ∘ τ .α.η  U
    ≈⟨ τ .counit-comp ⟩
    S.ε.η U
    ∎
  Comonad⇒-id-∘ τ σ .comult-comp {U} = begin
    R.δ.η U ∘ σ .α.η U ∘ τ .α.η U
    ≈⟨ C.sym-assoc ⟩
    (R.δ.η U ∘ σ .α.η U) ∘ τ .α.η U
    ≈⟨ σ .comult-comp ⟩∘⟨refl  ⟩
    (σ .α.η (R.F.₀ U) ∘ T.F.₁ (σ .α.η U) ∘ T.δ.η U) ∘ τ .α.η U
    ≈⟨ C.sym-assoc ⟩∘⟨refl
     ○ C.assoc ⟩
    (σ .α.η (R.F.₀ U) ∘ T.F.₁ (σ .α.η U)) ∘ (T.δ.η U ∘ τ .α.η U)
    ≈⟨ refl⟩∘⟨ τ .comult-comp ⟩
    (σ .α.η (R.F.₀ U) ∘ T.F.₁ (σ .α.η U)) ∘ (τ .α.η (T.F.₀ U) ∘ S.F.₁ (τ .α.η U) ∘ S.δ.η U)
    ≈⟨ C.assoc
     ○ refl⟩∘⟨ C.sym-assoc ⟩
    σ .α.η (R.F.₀ U) ∘ (T.F.₁ (σ .α.η U) ∘ τ .α.η (T.F.₀ U)) ∘ S.F.₁ (τ .α.η U) ∘ S.δ.η U
    ≈⟨ refl⟩∘⟨ τ .α .sym-commute (σ .α.η U) ⟩∘⟨refl  ⟩
    σ .α.η (R.F.₀ U) ∘ (τ .α.η (R.F.₀ U) ∘ S.F.₁ (σ .α.η U)) ∘ S.F.₁ (τ .α.η U) ∘ S.δ.η U
    ≈⟨ refl⟩∘⟨ C.assoc
     ○ C.sym-assoc
     ○ refl⟩∘⟨ C.sym-assoc ⟩
    (σ .α.η (R.F.₀ U) ∘ τ .α.η (R.F.₀ U)) ∘ (S.F.₁ (σ .α.η U) ∘ S.F.₁ (τ .α.η U)) ∘ S.δ.η U
    ≈⟨ refl⟩∘⟨ ⟺ S.F.homomorphism ⟩∘⟨refl ⟩
    (σ .α.η (R.F.₀ U) ∘ τ .α.η (R.F.₀ U)) ∘ S.F.₁ (σ .α.η U ∘ τ .α.η  U) ∘ S.δ.η U
    ∎
