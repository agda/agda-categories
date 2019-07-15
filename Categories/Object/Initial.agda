{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Object.Initial {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

open import Categories.Morphism C
open import Categories.Object.Terminal op

record Initial : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊥ : Obj
    ! : (A : Obj) → (⊥ ⇒ A)
    !-unique : ∀ {A} → (f : ⊥ ⇒ A) → ! A ≈ f

  !-unique₂ : ∀ {A} → (f g : ⊥ ⇒ A) → f ≈ g
  !-unique₂ {A} f g = begin
    f ≈˘⟨ !-unique f ⟩
    ! A ≈⟨ !-unique g ⟩
    g ∎
    where open HomReasoning

  ⊥-id : (f : ⊥ ⇒ ⊥) → f ≈ id
  ⊥-id f = !-unique₂ f id

open Initial

to-⊥-is-Epi : ∀ {A : Obj} {i : Initial} → (f : A ⇒ ⊥ i) → Epi f
to-⊥-is-Epi {_} {i} _ = λ g h _ → !-unique₂ i g h
