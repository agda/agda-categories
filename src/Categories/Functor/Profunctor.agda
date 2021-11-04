{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Profunctor where

open import Level

open import Data.Product
open import Relation.Binary.Bundles
open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Hom
open import Categories.Morphism.Reasoning as MR hiding (assoc²)

module Profunctor {o ℓ e} (C : Category o ℓ e) (D : Category o ℓ e) where

  Profunctor : ∀ {o ℓ e} {o′ ℓ′ e′} → Category o ℓ e → Category o′ ℓ′ e′ → Set _
  Profunctor {ℓ = ℓ} {e} {ℓ′ = ℓ′} {e′} C D = Bifunctor (Category.op D) C (Setoids (ℓ ⊔ ℓ′) (e ⊔ e′))

  id : ∀ {o ℓ e} → {C : Category o ℓ e} → Profunctor C C
  id {C = C} = Hom[ C ][-,-]

  -- representable profunctors
  -- hom(f,1)
  repˡ : (F : Functor C D) → Profunctor D C
  repˡ F = record
    { F₀ = λ (c , d) → record
      { Carrier = D [ F₀ c , d ]
      ; _≈_ = D._≈_
      ; isEquivalence = D.equiv
      }
    ; F₁ = λ (f , g) → record
      { _⟨$⟩_ = λ x → g ∘ x ∘ F₁ f
      ; cong = λ x → begin _ ≈⟨ refl⟩∘⟨ x ⟩∘⟨refl ⟩ _ ∎
      }
    ; identity = λ {x} {y} {y'} y≈y' → begin
        D.id ∘ y ∘ F₁ C.id ≈⟨ D.identityˡ ⟩
        y ∘ F₁ C.id        ≈⟨ elimʳ D identity ⟩
        y                  ≈⟨ y≈y' ⟩
        y'                 ∎
    ; homomorphism = λ { {f = f0 , f1} {g = g0 , g1} {x} {y} x≈y → begin
        (g1 ∘ f1) ∘ x ∘ F₁ (f0 C.∘ g0)  ≈⟨ refl⟩∘⟨ x≈y ⟩∘⟨ Functor.homomorphism F ⟩
        (g1 ∘ f1) ∘ y ∘ F₁ f0 ∘ F₁ g0   ≈⟨ refl⟩∘⟨ D.Equiv.sym D.assoc ⟩
        (g1 ∘ f1) ∘ (y ∘ F₁ f0) ∘ F₁ g0 ≈⟨ assoc²'' D ⟩
        g1 ∘ (f1 ∘ y ∘ F₁ f0) ∘ F₁ g0 ∎
      }
    ; F-resp-≈ = λ { {f = f0 , f1} {g = g0 , g1} (f0≈g0 , f1≈g1) {x} {y} x≈y → begin
        f1 ∘ x ∘ F₁ f0 ≈⟨ f1≈g1 ⟩∘⟨ x≈y ⟩∘⟨ F-resp-≈ f0≈g0 ⟩
        g1 ∘ y ∘ F₁ g0 ∎
      }
    }
    where
     module C = Category C
     open module D = Category D
     open module F = Functor F
     open D.HomReasoning

  -- hom(1,f)
  repʳ : (F : Functor C D) → Profunctor C D
  repʳ F = record
    { F₀ = λ (c , d) → record
      { Carrier = D [ c , F₀ d ]
      ; _≈_ = D._≈_
      ; isEquivalence = D.equiv
      }
    ; F₁ = λ (f , g) → record
      { _⟨$⟩_ = λ x → F₁ g ∘ x ∘ f
      ; cong = λ x → begin _ ≈⟨ refl⟩∘⟨ x ⟩∘⟨refl ⟩ _ ∎
      }
    ; identity = λ {x} {y} {y'} y≈y' → begin
        F₁ C.id ∘ y ∘ D.id ≈⟨ elimˡ D identity ⟩
        y ∘ D.id             ≈⟨ D.identityʳ ⟩
        y                    ≈⟨ y≈y' ⟩
        y'                   ∎
    ; homomorphism = λ { {f = f0 , f1} {g = g0 , g1} {x} {y} x≈y → begin
        F₁ (g1 C.∘ f1) ∘ x ∘ f0 ∘ g0    ≈⟨ refl⟩∘⟨ x≈y ⟩∘⟨refl ⟩
        F₁ (g1 C.∘ f1) ∘ y ∘ f0 ∘ g0    ≈⟨ Functor.homomorphism F ⟩∘⟨refl ⟩
        (F₁ g1 ∘ F₁ f1) ∘ y ∘ f0 ∘ g0 ≈⟨ D.assoc ⟩
        F₁ g1 ∘ F₁ f1 ∘ y ∘ f0 ∘ g0       ≈⟨ refl⟩∘⟨ D.Equiv.sym assoc² ⟩
        F₁ g1 ∘ ((F₁ f1 ∘ y) ∘ f0) ∘ g0   ≈⟨ refl⟩∘⟨ D.assoc ⟩∘⟨refl ⟩
        F₁ g1 ∘ (F₁ f1 ∘ y ∘ f0) ∘ g0 ∎
      }
    ; F-resp-≈ = λ { {f = f0 , f1} {g = g0 , g1} (f0≈g0 , f1≈g1) {x} {y} x≈y → begin
        F₁ f1 ∘ x ∘ f0 ≈⟨ F-resp-≈ f1≈g1 ⟩∘⟨ x≈y ⟩∘⟨ f0≈g0 ⟩
        F₁ g1 ∘ y ∘ g0 ∎
      }
    }
    where
      module C = Category C
      open module D = Category D
      open module F = Functor F
      open D.HomReasoning
      open import Categories.Morphism.Reasoning D using (assoc²)