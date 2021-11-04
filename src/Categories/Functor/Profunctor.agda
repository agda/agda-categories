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

module Profunctor {o ℓ e} (C : Category o ℓ e) (D : Category o ℓ e) where

  open import Categories.Morphism.Reasoning D as MR

  Profunctor : ∀ {o ℓ e} {o′ ℓ′ e′} → Category o ℓ e → Category o′ ℓ′ e′ → Set _
  Profunctor {ℓ = ℓ} {e} {ℓ′ = ℓ′} {e′} C D = Bifunctor (Category.op D) C (Setoids (ℓ ⊔ ℓ′) (e ⊔ e′))

  id : ∀ {o ℓ e} → {C : Category o ℓ e} → Profunctor C C
  id {C = C} = Hom[ C ][-,-]

  -- representable profunctor
  -- hom(f,1)
  repˡ : (F : Functor C D) → Profunctor {o} {ℓ} {e} {o} {ℓ} {e} D C
  repˡ F = record
    { F₀ = λ {(c , d) → record
        { Carrier = D [ Functor.F₀ F c , d ]
        ; _≈_ = D._≈_
        ; isEquivalence = D.equiv
        }}
    ; F₁ = λ { {A = A0 , A1} {B = B0 , B1} (f , g) → record
      { _⟨$⟩_ = λ x → g D.∘ x D.∘ Functor.F₁ F f
      ; cong = λ x → D.∘-resp-≈ D.Equiv.refl (D.∘-resp-≈ x D.Equiv.refl)
      }}
    ; identity = λ {x} {y} {y'} y≈y' → begin
      D.id D.∘ y D.∘ Functor.F₁ F C.id ≈⟨ D.identityˡ ⟩
      y D.∘ Functor.F₁ F C.id ≈⟨ (refl⟩∘⟨ Functor.identity F) ⟩
      y D.∘ D.id ≈⟨ D.Equiv.trans D.identityʳ y≈y' ⟩
      y' ∎
    ; homomorphism = λ { {X = X0 , X1} {Y = Y0 , Y1} {Z = Z0 , Z1} {f = f0 , f1} {g = g0 , g1} {x} {y} x≈y →
      begin
       (g1 D.∘ f1) D.∘ x D.∘ Functor.F₁ F (f0 C.∘ g0)              ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ Functor.homomorphism F)) ⟩
       (g1 D.∘ f1) D.∘ x D.∘ Functor.F₁ F f0 D.∘ Functor.F₁ F g0   ≈⟨ (refl⟩∘⟨ (x≈y ⟩∘⟨refl)) ⟩
       (g1 D.∘ f1) D.∘ y D.∘ Functor.F₁ F f0 D.∘ Functor.F₁ F g0   ≈⟨ (refl⟩∘⟨ D.Equiv.sym (Category.assoc D)) ⟩
       (g1 D.∘ f1) D.∘ (y D.∘ Functor.F₁ F f0) D.∘ Functor.F₁ F g0 ≈⟨ Category.assoc D ⟩
       g1 D.∘ f1 D.∘ (y D.∘ Functor.F₁ F f0) D.∘ Functor.F₁ F g0   ≈⟨ (refl⟩∘⟨ D.Equiv.sym (Category.assoc D)) ⟩
       g1 D.∘ (f1 D.∘ y D.∘ Functor.F₁ F f0) D.∘ Functor.F₁ F g0 ∎ }
    ; F-resp-≈ = resp
    }
    where
     module C = Category C
     module D = Category D
     open D.HomReasoning
     resp : {A B : Σ C.Obj (λ x → D.Obj)}
      {f g : Σ (proj₁ B C.⇒ proj₁ A) (λ x → proj₂ A D.⇒ proj₂ B)} →
      Σ (proj₁ f C.≈ proj₁ g) (λ x → proj₂ f D.≈ proj₂ g) →
      {x y : Functor.F₀ F (proj₁ A) D.⇒ proj₂ A} →
      x D.≈ y →
      proj₂ f D.∘ x D.∘ Functor.F₁ F (proj₁ f) D.≈
      proj₂ g D.∘ y D.∘ Functor.F₁ F (proj₁ g)
     resp {A = A0 , A1} {B = B0 , B1} {f = f0 , f1} {g = g0 , g1} (eq0 , eq1) {x} {y} eq' = begin
       f1 D.∘ x D.∘ Functor.F₁ F f0 ≈⟨ (refl⟩∘⟨ (eq' ⟩∘⟨refl)) ⟩
       f1 D.∘ y D.∘ Functor.F₁ F f0 ≈⟨ D.∘-resp-≈ eq1 D.Equiv.refl ⟩
       g1 D.∘ y D.∘ Functor.F₁ F f0 ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ Functor.F-resp-≈ F eq0)) ⟩
       g1 D.∘ y D.∘ Functor.F₁ F g0 ∎

  -- hom(1,f)
  repʳ : (F : Functor C D) → Profunctor C D
  repʳ F = record
    { F₀ = λ x → {!   !}
    ; F₁ = {!   !}
    ; identity = {!   !}
    ; homomorphism = {!   !}
    ; F-resp-≈ = {!   !}
    }
