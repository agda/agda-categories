{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core
open import Categories.Category.Monoidal.Core

module Categories.Category.Construction.Monoids {o ℓ e} {𝒞 : Category o ℓ e} (C : Monoidal 𝒞) where

open import Level

open import Categories.Functor using (Functor)
open import Categories.Morphism.Reasoning 𝒞
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
    ; preserves-μ = trans identityˡ (introʳ (Functor.identity ⊗))
    ; preserves-η = identityˡ
    }
  ; _∘_ = λ {A B C} f g → record
    { arr = arr f ∘ arr g
    ; preserves-μ = begin
      (arr f ∘ arr g) ∘ μ A
        ≈⟨ pullʳ (preserves-μ g) ⟩
      arr f ∘ (μ B ∘ arr g ⊗₁ arr g)
        ≈⟨ pullˡ (preserves-μ f) ⟩
      (μ C ∘ arr f ⊗₁ arr f) ∘ arr g ⊗₁ arr g
        ≈⟨ pullʳ (sym (Functor.homomorphism ⊗)) ⟩
      μ C ∘ (arr f ∘ arr g) ⊗₁ (arr f ∘ arr g)
        ∎
    ; preserves-η = trans (pullʳ (preserves-η g)) (preserves-η f)
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
