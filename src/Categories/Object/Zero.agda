{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- a zero object is both terminal and initial.
module Categories.Object.Zero {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Categories.Object.Terminal C
open import Categories.Object.Initial C

open import Categories.Morphism C
open import Categories.Morphism.Reasoning C

open Category C
open HomReasoning

record IsZero (Z : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    isInitial : IsInitial Z
    isTerminal : IsTerminal Z

  open IsInitial isInitial public
    renaming
    ( ! to ¡
    ; !-unique to ¡-unique
    ; !-unique₂ to ¡-unique₂
    )
  open IsTerminal isTerminal public

  zero⇒ : ∀ {A B : Obj} → A ⇒ B
  zero⇒ = ¡ ∘ !

  zero-∘ˡ : ∀ {X Y Z} → (f : Y ⇒ Z) → f ∘ zero⇒ {X} ≈ zero⇒
  zero-∘ˡ f = pullˡ (⟺ (¡-unique (f ∘ ¡)))

  zero-∘ʳ : ∀ {X Y Z} → (f : X ⇒ Y) → zero⇒ {Y} {Z} ∘ f ≈ zero⇒
  zero-∘ʳ f = pullʳ (⟺ (!-unique (! ∘ f)))

record Zero : Set (o ⊔ ℓ ⊔ e) where
  field
    𝟘 : Obj
    isZero : IsZero 𝟘

  open IsZero isZero public

  terminal : Terminal
  terminal = record { ⊤-is-terminal = isTerminal }

  initial : Initial
  initial = record { ⊥-is-initial = isInitial }

open Zero

¡-Mono : ∀ {A} {z : Zero} → Mono (¡ z {A})
¡-Mono {z = z} = from-⊤-is-Mono {t = terminal z} (¡ z)

!-Epi : ∀ {A} {z : Zero} → Epi (! z {A})
!-Epi {z = z} = to-⊥-is-Epi {i = initial z} (! z)
