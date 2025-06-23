{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Endofunctor; Functor)

module Categories.Monad.Distributive {o ℓ e} (C : Category o ℓ e) (F : Endofunctor C) where

open import Categories.Category.Construction.F-Coalgebras using (F-Coalgebras)
open import Categories.Functor.Coalgebra using (F-Coalgebra; F-Coalgebra-Morphism)
open import Categories.Functor.DistributiveLaw using (DistributiveLaw)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.Monad using (Monad) renaming (id to idM)
open import Categories.Morphism.Reasoning C
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Level using (_⊔_)

private
  module C = Category C
  module F = Functor F

open C using (_∘_; _≈_)
open C.HomReasoning

record DistributiveMonad : Set (o ⊔ ℓ ⊔ e) where
  field
    monad : Monad C
  open Monad monad public renaming (F to N; module F to N)
  field
    distrib : DistributiveLaw N F
  module distrib = NaturalTransformation distrib

  field
    η-distrib : ∀ {A} → distrib.η A ∘ η.η (F.F₀ A) ≈ F.₁ (η.η A)
    μ-distrib : ∀ {A} → distrib.η A ∘ μ.η (F.₀ A) ≈ (F.₁ (μ.η A) ∘ distrib.η (N.₀ A)) ∘ N.₁ (distrib.η A)

  -- An F-distributive monad lifts to a monad on F-coalgebras
  lifted : Monad (F-Coalgebras F)
  lifted = record
    { F = record
      { F₀ = λ X → record
        { A = N.₀ (F-Coalgebra.A X)
        ; α = distrib.η _ ∘ N.₁ (F-Coalgebra.α X)
        }
      ; F₁ = λ f → record
        { f = N.₁ (F-Coalgebra-Morphism.f f)
        ; commutes = glue
          (distrib.commute (F-Coalgebra-Morphism.f f))
          ([ N ]-resp-square (F-Coalgebra-Morphism.commutes f))
        }
      ; identity = N.identity
      ; homomorphism = N.homomorphism
      ; F-resp-≈ = N.F-resp-≈
      }
    ; η = record
      { η = λ X → record
        { f = η.η _
        ; commutes = glue◃◽ η-distrib (η.sym-commute _)
        }
      ; commute = λ _ → η.commute _
      ; sym-commute = λ _ → η.sym-commute _
      }
    ; μ = record
      { η = λ X → record
        { f = μ.η _
        ; commutes = begin
          (distrib.η _ ∘ N.₁ _) ∘ μ.η _                                   ≈⟨ pullʳ (μ.sym-commute _) ⟩
          distrib.η _ ∘ (μ.η _ ∘ N.₁ (N.₁ _))                             ≈⟨ pullˡ μ-distrib ⟩
          ((F.₁ (μ.η _) ∘ distrib.η _) ∘ N.₁ (distrib.η _)) ∘ N.₁ (N.₁ _) ≈⟨ pullʳ (C.Equiv.sym N.homomorphism) ⟩
          (F.₁ (μ.η _) ∘ distrib.η _) ∘ N.₁ (distrib.η _ ∘ N.₁ _)         ≈⟨ C.assoc ⟩
          F.₁ (μ.η _) ∘ distrib.η _ ∘ N.₁ (distrib.η _ ∘ N.₁ _)           ∎
        }
      ; commute = λ _ → μ.commute _
      ; sym-commute = λ _ → μ.sym-commute _
      }
    ; assoc = assoc
    ; sym-assoc = sym-assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    }

-- The identity monad distributes over any functor
id : DistributiveMonad
id = record
  { monad = idM C
  ; distrib = record
    { η = λ _ → C.id
    ; commute = λ _ → id-comm-sym
    ; sym-commute = λ _ → id-comm
    }
  ; η-distrib = begin
    C.id C.∘ C.id ≈⟨ C.identity² ⟩
    C.id          ≈⟨ F.identity ⟨
    F.₁ C.id      ∎
  ; μ-distrib = C.∘-resp-≈ˡ (introˡ F.identity)
  }
