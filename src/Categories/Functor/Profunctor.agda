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
open import Categories.NaturalTransformation

Profunctor : ∀ {o ℓ e} {o′ ℓ′ e′} → Category o ℓ e → Category o′ ℓ′ e′ → Set _
Profunctor {ℓ = ℓ} {e} {ℓ′ = ℓ′} {e′} C D = Bifunctor (Category.op D) C (Setoids (ℓ ⊔ ℓ′) (e ⊔ e′))

-- Calling the profunctor identity "id" is a bad idea
proid : ∀ {o ℓ e} → {C : Category o ℓ e} → Profunctor C C
proid {C = C} = Hom[ C ][-,-]

module Profunctor {o ℓ e} {o′} (C : Category o ℓ e) (D : Category o′ ℓ e) where
  module C = Category C
  open module D = Category D
  open D.HomReasoning
  open import Categories.Morphism.Reasoning D using (assoc²''; elimˡ; elimʳ)

  -- representable profunctors
  -- hom(f,1)
  repˡ : ∀ (F : Functor C D) → Profunctor D C
  repˡ F = record
    { F₀ = λ (c , d) → record
      { Carrier = D [ F₀ c , d ]
      ; _≈_ = D._≈_
      ; isEquivalence = D.equiv
      }
    ; F₁ = λ (f , g) → record
      { _⟨$⟩_ = λ x → g ∘ x ∘ F₁ f
      ; cong  = λ x → begin _ ≈⟨ refl⟩∘⟨ x ⟩∘⟨refl ⟩ _ ∎
      }
    ; identity = λ {x} {y} {y'} y≈y' → begin
        D.id ∘ y ∘ F₁ C.id ≈⟨ D.identityˡ ⟩
        y ∘ F₁ C.id        ≈⟨ elimʳ identity ⟩
        y                  ≈⟨ y≈y' ⟩
        y'                 ∎
    ; homomorphism = λ { {f = f0 , f1} {g = g0 , g1} {x} {y} x≈y → begin
        (g1 ∘ f1) ∘ x ∘ F₁ (f0 C.∘ g0)  ≈⟨ refl⟩∘⟨ x≈y ⟩∘⟨ F.homomorphism ⟩
        (g1 ∘ f1) ∘ y ∘ F₁ f0 ∘ F₁ g0   ≈⟨ refl⟩∘⟨ D.sym-assoc ⟩
        (g1 ∘ f1) ∘ (y ∘ F₁ f0) ∘ F₁ g0 ≈⟨ assoc²'' ⟩
        g1 ∘ (f1 ∘ y ∘ F₁ f0) ∘ F₁ g0 ∎
      }
    ; F-resp-≈ = λ { {f = f0 , f1} {g = g0 , g1} (f0≈g0 , f1≈g1) {x} {y} x≈y → begin
        f1 ∘ x ∘ F₁ f0 ≈⟨ f1≈g1 ⟩∘⟨ x≈y ⟩∘⟨ F-resp-≈ f0≈g0 ⟩
        g1 ∘ y ∘ F₁ g0 ∎
      }
    }
    where
      open module F = Functor F

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
      ; cong  = λ x → begin _ ≈⟨ refl⟩∘⟨ x ⟩∘⟨refl ⟩ _ ∎
      }
    ; identity = λ {x} {y} {y'} y≈y' → begin
        F₁ C.id ∘ y ∘ D.id ≈⟨ elimˡ identity ⟩
        y ∘ D.id           ≈⟨ D.identityʳ ⟩
        y                  ≈⟨ y≈y' ⟩
        y'                 ∎
    ; homomorphism = λ { {f = f0 , f1} {g = g0 , g1} {x} {y} x≈y → begin
        F₁ (g1 C.∘ f1) ∘ x ∘ f0 ∘ g0    ≈⟨ F.homomorphism ⟩∘⟨ x≈y ⟩∘⟨refl ⟩
        (F₁ g1 ∘ F₁ f1) ∘ y ∘ f0 ∘ g0   ≈⟨ refl⟩∘⟨ D.sym-assoc ⟩
        (F₁ g1 ∘ F₁ f1) ∘ (y ∘ f0) ∘ g0 ≈⟨ assoc²'' ⟩
        F₁ g1 ∘ (F₁ f1 ∘ y ∘ f0) ∘ g0   ∎
      }
    ; F-resp-≈ = λ { {f = f0 , f1} {g = g0 , g1} (f0≈g0 , f1≈g1) {x} {y} x≈y → begin
        F₁ f1 ∘ x ∘ f0 ≈⟨ F-resp-≈ f1≈g1 ⟩∘⟨ x≈y ⟩∘⟨ f0≈g0 ⟩
        F₁ g1 ∘ y ∘ g0 ∎
      }
    }
    where
      open module F = Functor F

  -- each Prof(C,D) is a category
  homProf : (C : Category o ℓ e) → (D : Category o′ ℓ e) → Category _ _ e
  homProf C D = record
    { Obj = Profunctor C D
    ; _⇒_ = λ P Q → NaturalTransformation P Q
    ; _≈_ = λ α β → {!    !} -- equality of nat transf
    ; id = Categories.NaturalTransformation.id
    ; _∘_ = _∘ᵥ_
    ; assoc = λ {A} {B} {C₂} {D₂} {f} {g} {h} → {!   !}
    ; sym-assoc = {!   !}
    ; identityˡ = {!   !}
    ; identityʳ = {!   !}
    ; identity² = {!   !}
    ; equiv = {!   !}
    ; ∘-resp-≈ = {!   !}
    }