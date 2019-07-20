{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Construction.LiftSetoids where

open import Level
open import Relation.Binary
open import Function.Equality

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor

private
  variable
    c ℓ : Level

LiftedSetoid : ∀ c′ ℓ′ → Setoid c ℓ → Setoid (c ⊔ c′) (ℓ ⊔ ℓ′)
LiftedSetoid c′ ℓ′ S = record
  { Carrier       = Lift c′ Carrier
  ; _≈_           = λ x y → Lift ℓ′ (lower x ≈ lower y)
  ; isEquivalence = record
    { refl  = lift refl
    ; sym   = λ eq → lift (sym (lower eq))
    ; trans = λ eq eq′ → lift (trans (lower eq) (lower eq′))
    }
  }
  where open Setoid S

LiftSetoids : ∀ c′ ℓ′ → Functor (Setoids c ℓ) (Setoids (c ⊔ c′) (ℓ ⊔ ℓ′))
LiftSetoids c′ ℓ′ = record
  { F₀           = LiftedSetoid c′ ℓ′
  ; F₁           = λ f → record
    { _⟨$⟩_ = λ x → lift (f ⟨$⟩ lower x)
    ; cong  = λ eq → lift (cong f (lower eq))
    }
  ; identity     = λ eq → eq
  ; homomorphism = λ {_ _ _ f g} eq → lift (cong g (cong f (lower eq)))
  ; F-resp-≈     = λ eq eq′ → lift (eq (lower eq′))
  }
