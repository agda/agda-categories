{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Endofunctor; Functor)

module Categories.Comonad.Distributive {o ℓ e} (C : Category o ℓ e) (F : Endofunctor C) where

open import Categories.Category.Construction.F-Algebras using (F-Algebras)
open import Categories.Comonad using (Comonad) renaming (id to idW)
open import Categories.Functor.Algebra using (F-Algebra; F-Algebra-Morphism)
open import Categories.Functor.DistributiveLaw using (DistributiveLaw)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.Morphism.Reasoning C
open import Categories.NaturalTransformation using (NaturalTransformation)

open import Level using (_⊔_)

private
  module C = Category C
  module F = Functor F

open C using (_∘_; _≈_)
open C.HomReasoning

record DistributiveComonad : Set (o ⊔ ℓ ⊔ e) where
  field
    comonad : Comonad C
  open Comonad comonad public renaming (F to N; module F to N)
  field
    distrib : DistributiveLaw F N
  module distrib = NaturalTransformation distrib

  field
    ε-distrib : ∀ {A} → ε.η (F.₀ A) ∘ distrib.η A ≈ F.₁ (ε.η A)
    δ-distrib : ∀ {A} → δ.η (F.₀ A) ∘ distrib.η A ≈ N.₁ (distrib.η A) ∘ distrib.η (N.₀ A) ∘ F.₁ (δ.η A)

  -- An F-distributive comonad lifts to a comonad on F-algebras
  lifted : Comonad (F-Algebras F)
  lifted = record
    { F = record
      { F₀ = λ X → record
        { A = N.₀ (F-Algebra.A X)
        ; α = N.₁ (F-Algebra.α X) ∘ distrib.η _
        }
      ; F₁ = λ f → record
        { f = N.₁ (F-Algebra-Morphism.f f)
        ; commutes = glue′
          ([ N ]-resp-square (F-Algebra-Morphism.commutes f))
          (distrib.sym-commute (F-Algebra-Morphism.f f))
        }
      ; identity = N.identity
      ; homomorphism = N.homomorphism
      ; F-resp-≈ = N.F-resp-≈
      }
    ; ε = record
      { η = λ X → record
        { f = ε.η _
        ; commutes = glue◽◃ (ε.commute _) ε-distrib
        }
      ; commute = λ f → ε.commute _
      ; sym-commute = λ f → ε.sym-commute _
      }
    ; δ = record
      { η = λ X → record
        { f = δ.η _
        ; commutes = begin
          δ.η _ ∘ (N.₁ _ ∘ distrib.η _)                                   ≈⟨ glue◽◃ (δ.commute _) δ-distrib ⟩
          N.₁ (N.₁ _) ∘ (N.₁ (distrib.η _) ∘ (distrib.η _ ∘ F.₁ (δ.η _))) ≈⟨ pullˡ (C.Equiv.sym N.homomorphism) ⟩
          N.₁ (N.₁ _ ∘ distrib.η _) ∘ (distrib.η _ ∘ F.₁ (δ.η _))         ≈⟨ C.sym-assoc ⟩
          (N.₁ (N.₁ _ ∘ distrib.η _) ∘ distrib.η _) ∘ F.₁ (δ.η _)         ∎
        }
      ; commute = λ f → δ.commute _
      ; sym-commute = λ f → δ.sym-commute _
      }
    ; assoc = assoc
    ; sym-assoc = sym-assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    }

-- The identity comonad distributes over any endofunctor
id : DistributiveComonad
id = record
  { comonad = idW C
  ; distrib = record
    { η = λ X → C.id
    ; commute = λ _ → id-comm-sym
    ; sym-commute = λ _ → id-comm
    }
  ; ε-distrib = begin
    C.id C.∘ C.id ≈⟨ C.identity² ⟩
    C.id          ≈⟨ F.identity ⟨
    F.₁ C.id      ∎
  ; δ-distrib = C.∘-resp-≈ʳ (introʳ F.identity)
  }
