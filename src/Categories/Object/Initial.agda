{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Object.Initial {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Category C
open import Categories.Morphism C using (Epi; _≅_)
open import Categories.Morphism.IsoEquiv C using (_≃_; ⌞_⌟)
open import Categories.Morphism.Reasoning C

open HomReasoning

record IsInitial (⊥ : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    ! : {A : Obj} → (⊥ ⇒ A)
    !-unique : ∀ {A} → (f : ⊥ ⇒ A) → ! ≈ f

  !-unique₂ : ∀ {A} → (f g : ⊥ ⇒ A) → f ≈ g
  !-unique₂ f g = begin
    f ≈˘⟨ !-unique f ⟩
    ! ≈⟨ !-unique g ⟩
    g ∎
    where open HomReasoning

  ⊥-id : (f : ⊥ ⇒ ⊥) → f ≈ id
  ⊥-id f = !-unique₂ f id

record Initial : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊥ : Obj
    ⊥-is-initial : IsInitial ⊥

  open IsInitial ⊥-is-initial public

open Initial

to-⊥-is-Epi : ∀ {A : Obj} {i : Initial} → (f : A ⇒ ⊥ i) → Epi f
to-⊥-is-Epi {_} {i} _ = λ g h _ → !-unique₂ i g h

up-to-iso : (i₁ i₂ : Initial) → ⊥ i₁ ≅ ⊥ i₂
up-to-iso i₁ i₂ = record
  { from = ! i₁
  ; to   = ! i₂
  ; iso  = record { isoˡ = ⊥-id i₁ _; isoʳ = ⊥-id i₂ _ }
  }

transport-by-iso : (i : Initial) → ∀ {X} → ⊥ i ≅ X → Initial
transport-by-iso i {X} i≅X = record
  { ⊥        = X
  ; ⊥-is-initial = record
    { !        = ! i ∘ to
    ; !-unique = λ h →  begin
      ! i ∘ to        ≈⟨ !-unique i (h ∘ from) ⟩∘⟨refl  ⟩
      (h ∘ from) ∘ to ≈⟨ cancelʳ isoʳ ⟩
      h              ∎
    }
  }
  where open _≅_ i≅X

up-to-iso-unique : ∀ i i′ → (iso : ⊥ i ≅ ⊥ i′) → up-to-iso i i′ ≃ iso
up-to-iso-unique i i′ iso = ⌞ !-unique i _ ⌟

up-to-iso-invˡ : ∀ {t X} {i : ⊥ t ≅ X} → up-to-iso t (transport-by-iso t i) ≃ i
up-to-iso-invˡ {t} {i = i} = up-to-iso-unique t (transport-by-iso t i) i

up-to-iso-invʳ : ∀ {t t′} → ⊥ (transport-by-iso t (up-to-iso t t′)) ≡ ⊥ t′
up-to-iso-invʳ {t} {t′} = ≡.refl
