{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core
open import Categories.Category.Monoidal.Core

module Categories.Category.Construction.Monoids {o ℓ e} {𝒞 : Category o ℓ e} (C : Monoidal 𝒞) where

open import Level

open import Categories.Functor using (Functor)
open import Categories.Object.Monoid C

open Category 𝒞
open Monoidal C
open HomReasoning
open Monoid using (η; μ)
open Monoid⇒

Monoids : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
Monoids = record
  { Obj = Monoid
  ; _⇒_ = Monoid⇒
  ; _≈_ = λ f g → arr f ≈ arr g
  ; id = λ {A} → record
    { arr = id
    ; preserves-μ = begin
      id ∘ μ A
        ≈⟨ identityˡ ⟩
      μ A
        ≈⟨ sym identityʳ ⟩
      μ A ∘ id
        ≈⟨ (refl ⟩∘⟨ sym (Functor.identity ⊗)) ⟩
      μ A ∘ id ⊗₁ id
        ∎
    ; preserves-η = identityˡ
    }
  ; _∘_ = λ {A B C} f g → record
    { arr = arr f ∘ arr g
    ; preserves-μ = begin
      (arr f ∘ arr g) ∘ μ A
        ≈⟨ assoc ⟩
      arr f ∘ (arr g ∘ μ A)
        ≈⟨ (refl⟩∘⟨ preserves-μ g) ⟩
      arr f ∘ (μ B ∘ arr g ⊗₁ arr g)
        ≈⟨ sym assoc ⟩
      (arr f ∘ μ B) ∘ arr g ⊗₁ arr g
        ≈⟨ (preserves-μ f ⟩∘⟨refl) ⟩
      (μ C ∘ arr f ⊗₁ arr f) ∘ arr g ⊗₁ arr g
        ≈⟨ assoc ⟩
      μ C ∘ (arr f ⊗₁ arr f ∘ arr g ⊗₁ arr g)
        ≈⟨ (refl⟩∘⟨ sym (Functor.homomorphism ⊗)) ⟩
      μ C ∘ (arr f ∘ arr g) ⊗₁ (arr f ∘ arr g)
        ∎
    ; preserves-η = begin
      (arr f ∘ arr g) ∘ η A
        ≈⟨ assoc ⟩
      arr f ∘ (arr g ∘ η A)
        ≈⟨ (refl⟩∘⟨ preserves-η g) ⟩
      arr f ∘ η B
        ≈⟨ preserves-η f ⟩
      η C
        ∎
    }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≈ = ∘-resp-≈
  }
