{-# OPTIONS --without-K --safe #-}
module Categories.Category.Dagger where

open import Level using (_⊔_; suc)
open import Relation.Unary using (Pred)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Morphism using (Iso)

record HasDagger {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  infix 10 _†

  field
    _† : ∀ {A B} → A ⇒ B → B ⇒ A
    †-identity : ∀ {A} → id {A} † ≈ id
    †-homomorphism : ∀ {A B C} {f : A ⇒ B} {g : B ⇒ C} → (g ∘ f) † ≈ f † ∘ g †
    †-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ g → f † ≈ g †
    †-involutive : ∀ {A B} (f : A ⇒ B) → f † † ≈ f

  †-Functor : Functor op C
  †-Functor = record
    { F₀ = λ A → A
    ; F₁ = _†
    ; identity = †-identity
    ; homomorphism = †-homomorphism
    ; F-resp-≈ = †-resp-≈
    }

  isUnitary : ∀ {A B} → Pred (A ⇒ B) e
  isUnitary f = Iso C f (f †)

  isSelfAdjoint : ∀ {A} → Pred (A ⇒ A) e
  isSelfAdjoint f = f † ≈ f

record DaggerCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    C : Category o ℓ e
    hasDagger : HasDagger C

  open Category C public
  open HasDagger hasDagger public
