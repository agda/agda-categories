{-# OPTIONS --without-K --safe #-}

module Categories.Category.Lift where

open import Level
open import Categories.Category
open import Categories.Functor using (Functor)

liftC : ∀ {o ℓ e} o′ ℓ′ e′ → Category o ℓ e → Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
liftC o′ ℓ′ e′ C = record
  { Obj       = Lift o′ Obj
  ; _⇒_       = λ X Y → Lift ℓ′ (lower X ⇒ lower Y)
  ; _≈_       = λ f g → Lift e′ (lower f ≈ lower g)
  ; id        = lift id
  ; _∘_       = λ f g → lift (lower f ∘ lower g)
  ; assoc     = lift assoc
  ; sym-assoc = lift sym-assoc
  ; identityˡ = lift identityˡ
  ; identityʳ = lift identityʳ
  ; identity² = lift identity²
  ; equiv     = record
    { refl  = lift Equiv.refl
    ; sym   = λ eq → lift (Equiv.sym (lower eq))
    ; trans = λ eq eq′ → lift (Equiv.trans (lower eq) (lower eq′))
    }
  ; ∘-resp-≈  = λ eq eq′ → lift (∘-resp-≈ (lower eq) (lower eq′))
  }
  where open Category C

liftF : ∀ {o ℓ e} o′ ℓ′ e′ (C : Category o ℓ e) → Functor C (liftC o′ ℓ′ e′ C)
liftF  o′ ℓ′ e′ C = record
  { F₀           = lift
  ; F₁           = lift
  ; identity     = lift refl
  ; homomorphism = lift refl
  ; F-resp-≈     = lift
  }
  where open Category C
        open Equiv

unliftF : ∀ {o ℓ e} o′ ℓ′ e′ (C : Category o ℓ e) → Functor (liftC o′ ℓ′ e′ C) C
unliftF o′ ℓ′ e′ C = record
  { F₀           = lower
  ; F₁           = lower
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = lower
  }
  where open Category C
        open Equiv
