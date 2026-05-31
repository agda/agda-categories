{-# OPTIONS --without-K --safe #-}

-- Some properties of 'heterogeneous' identity morphisms

module Categories.Morphism.HeterogeneousIdentity.Properties where

open import Level
open import Data.Product using (curry) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Product
open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Morphism.HeterogeneousIdentity

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴ : Level

open Category using (Obj; id)

-- Functor identity laws lifted to heterogeneous identities.

hid-identity : (C : Category o ℓ e) (D : Category o′ ℓ′ e′)
               {F₀ : Obj C → Obj D}
               (F₁ : ∀ {A B} → C [ A , B ] → D [ F₀ A , F₀ B ]) →
               (∀ {A} → D [ F₁ (id C {A}) ≈ id D ]) →
               ∀ {A B} (p : A ≡ B) → D [ F₁ (hid C p) ≈ hid D (cong F₀ p) ]
hid-identity C D F₁ hyp refl = hyp

hid-identity₂ : (C₁ : Category o ℓ e) (C₂ : Category o′ ℓ′ e′)
                (D : Category o″ ℓ″ e″)
                {F₀ : Obj C₁ → Obj C₂ → Obj D}
                (F₁ : ∀ {A₁ A₂ B₁ B₂} → C₁ [ A₁ , B₁ ] → C₂ [ A₂ , B₂ ] →
                      D [ F₀ A₁ A₂ , F₀ B₁ B₂ ]) →
                (∀ {A₁ A₂} → D [ F₁ (id C₁ {A₁}) (id C₂ {A₂}) ≈ id D ]) →
                ∀ {A₁ A₂ B₁ B₂} (p : A₁ ≡ B₁) (q : A₂ ≡ B₂) →
                D [ F₁ (hid C₁ p) (hid C₂ q) ≈ hid D (cong₂ F₀ p q) ]
hid-identity₂ C₁ C₂ D F₁ hyp refl refl = hyp

module _ {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
         (F : Functor C D) where
  open Category D
  open Functor F

  -- functors preserve heterogeneous identities

  F-hid : ∀ {A B} (p : A ≡ B) → F₁ (hid C p) ≈ hid D (cong F₀ p)
  F-hid = hid-identity C D F₁ identity

module _ {C₁ : Category o ℓ e} {C₂ : Category o′ ℓ′ e′}
         {D : Category o″ ℓ″ e″} (F : Bifunctor C₁ C₂ D) where
  open Category D
  open Functor F

  -- bifunctors preserve heterogeneous identities

  BF-hid : ∀ {A₁ A₂ B₁ B₂} (p : A₁ ≡ B₁) (q : A₂ ≡ B₂) →
           F₁ (hid C₁ p ,, hid C₂ q) ≈ hid D (cong₂ (curry F₀) p q)
  BF-hid = hid-identity₂ C₁ C₂ D (curry F₁) identity

module _ (C : Category o ℓ e) (D : Category o′ ℓ′ e′) where
  open Category (Product C D)

  -- products preserve heterogeneous identities

  ×-hid : ∀ {A₁ A₂ B₁ B₂} (p : A₁ ≡ B₁) (q : A₂ ≡ B₂) →
          (hid C p ,, hid D q) ≈ hid (Product C D) (cong₂ _,,_ p q)
  ×-hid p q = BF-hid {C₁ = C} {C₂ = D} (idF ⁂ idF) p q
