{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Object.Terminal {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Relation.Binary using (IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Morphisms C
open import Categories.Square C

open Category C
open HomReasoning

record Terminal : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊤ : Obj
    ! : ∀ {A} → (A ⇒ ⊤)
    !-unique : ∀ {A} → (f : A ⇒ ⊤) → ! ≈ f

  !-unique₂ : ∀ {A} → (f g : A ⇒ ⊤) → f ≈ g
  !-unique₂ f g = begin
    f ≈⟨ Equiv.sym (!-unique f) ⟩
    ! ≈⟨ !-unique g ⟩
    g ∎
    where open HomReasoning

  ⊤-id : (f : ⊤ ⇒ ⊤) → f ≈ id
  ⊤-id f = !-unique₂ f id

open Terminal

from-⊤-is-Mono : ∀ {A : Obj} {t : Terminal} → (f : ⊤ t ⇒ A) → Mono f
from-⊤-is-Mono {_} {t} f = helper
  where
    helper : ∀ {C : Obj} -> (g h : C ⇒ ⊤ t) → f ∘ g ≈ f ∘ h → g ≈ h
    helper g h _ = !-unique₂ t g h

up-to-iso : (t₁ t₂ : Terminal) → ⊤ t₁ ≅ ⊤ t₂
up-to-iso t₁ t₂ = record
  { from = ! t₂
  ; to   = ! t₁
  ; iso  = record { isoˡ = ⊤-id t₁ _; isoʳ = ⊤-id t₂ _ }
  }

transport-by-iso : (t : Terminal) → ∀ {X} → ⊤ t ≅ X → Terminal
transport-by-iso t {X} t≅X = record
  { ⊤        = X
  ; !        = from ∘ ! t
  ; !-unique = λ h → begin
    from ∘ ! t    ≈⟨ refl⟩∘⟨ !-unique t (to ∘ h)  ⟩
    from ∘ to ∘ h ≈⟨ cancelLeft isoʳ ⟩
    h             ∎
  }
  where open _≅_ t≅X

up-to-iso-unique : ∀ t t′ → (i : ⊤ t ≅ ⊤ t′) → up-to-iso t t′ ≃ i
up-to-iso-unique t t′ i = record
  { from-≈ = !-unique t′ _
  ; to-≈   = !-unique t _
  }

up-to-iso-invˡ : ∀ {t X} {i : ⊤ t ≅ X} → up-to-iso t (transport-by-iso t i) ≃ i
up-to-iso-invˡ {t} {i = i} = up-to-iso-unique t (transport-by-iso t i) i

up-to-iso-invʳ : ∀ {t t′} → ⊤ (transport-by-iso t (up-to-iso t t′)) ≡ ⊤ t′
up-to-iso-invʳ {t} {t′} = ≡.refl
