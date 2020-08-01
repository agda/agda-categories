{-# OPTIONS --without-K --safe #-}

-- The category build from ObjectRestriction can be done so Functorially

module Categories.Functor.Construction.ObjectRestriction where

open import Level
open import Data.Product using (proj₁)
open import Relation.Unary using (Pred)
open import Function using () renaming (id to id→)

open import Categories.Category.Core
open import Categories.Category.Construction.ObjectRestriction
open import Categories.Functor.Core
open import Categories.Functor.Properties using (Faithful; Full)

private
  variable
    o ℓ e ℓ′ : Level
    C : Category o ℓ e

RestrictionFunctor : {ℓ′ : Level} → (C : Category o ℓ e) → (E : Pred (Category.Obj C) ℓ′) → Functor (ObjectRestriction C E) C
RestrictionFunctor C E = record
  { F₀ = proj₁
  ; F₁ = id→
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = id→
  }
  where
  open Category C

RF-Faithful : {E : Pred (Category.Obj C) ℓ′} → Faithful (RestrictionFunctor C E)
RF-Faithful _ _ = id→

RF-Full : {E : Pred (Category.Obj C) ℓ′} → Full (RestrictionFunctor C E)
RF-Full {C = C} = record
  { from = record
    { _⟨$⟩_ = id→
    ; cong = id→
    }
  ; right-inverse-of = λ _ → Category.Equiv.refl C
  }
