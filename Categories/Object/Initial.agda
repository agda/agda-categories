{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Object.Initial {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

open import Categories.Morphisms C
open import Categories.Object.Terminal op

record Initial : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊥ : Obj
    ! : ∀ {A} → (⊥ ⇒ A)
    !-unique : ∀ {A} → (f : ⊥ ⇒ A) → ! ≈ f

  !-unique₂ : ∀ {A} → (f g : ⊥ ⇒ A) → f ≈ g
  !-unique₂ f g = begin
    f ≈⟨ Equiv.sym (!-unique f) ⟩
    ! ≈⟨ !-unique g ⟩
    g ∎
    where open HomReasoning

  ⊥-id : (f : ⊥ ⇒ ⊥) → f ≈ id
  ⊥-id f = !-unique₂ f id

module _ where
  open Initial
  
  to-⊥-is-Epi : ∀ {A : Obj} {i : Initial} → (f : A ⇒ ⊥ i) → Epi f
  to-⊥-is-Epi {_} {i} f = helper
    where
      helper : ∀ {C : Obj} → (g h : ⊥ i ⇒ C) → g ∘ f ≈ h ∘ f → g ≈ h
      helper g h _ = !-unique₂ i g h
  
⊥⇒op⊤ : Initial → Terminal
⊥⇒op⊤ i = record
  { ⊤        = ⊥
  ; !        = !
  ; !-unique = !-unique
  }
  where open Initial i

op⊤⇒⊥ : Terminal → Initial
op⊤⇒⊥ t = record
  { ⊥        = ⊤
  ; !        = !
  ; !-unique = !-unique
  }
  where open Terminal t

