{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Construction.LiftSetoids where

open import Level using (Level; _⊔_; Lift; lift)
open import Relation.Binary.Bundles using (Setoid)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function using (_$_) renaming (id to idf)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Core using (Functor)

open Func

private
  variable
    c ℓ : Level

-- Use pattern-matching (instead of explicit calls to lower) to minimize the
-- number of needed parens, and also make it syntactically apparent that
-- this is indeed just a Lift.
LiftedSetoid : ∀ c′ ℓ′ → Setoid c ℓ → Setoid (c ⊔ c′) (ℓ ⊔ ℓ′)
LiftedSetoid c′ ℓ′ S = record
  { Carrier       = Lift c′ Carrier
  ; _≈_           = λ where (lift x) (lift y) → Lift ℓ′ $ x ≈ y
  ; isEquivalence = record
    { refl  = lift refl
    ; sym   = λ where (lift eq)            → lift $ sym eq
    ; trans = λ where (lift eq) (lift eq′) → lift $ trans eq eq′
    }
  }
  where open Setoid S

LiftSetoids : ∀ c′ ℓ′ → Functor (Setoids c ℓ) (Setoids (c ⊔ c′) (ℓ ⊔ ℓ′))
LiftSetoids c′ ℓ′ = record
  { F₀           = LiftedSetoid c′ ℓ′
  ; F₁           = λ f → record
    { to    = λ where (lift x)  → lift $ f ⟨$⟩ x
    ; cong  = λ where (lift eq) → lift $ cong f eq
    }
  ; identity     = λ {A} → lift $ refl A
  ; homomorphism = λ {_} {_} {Z} → lift $ refl Z
  ; F-resp-≈     = λ f≈g → lift f≈g
  }
  where
    open Setoid
