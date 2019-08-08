{-# OPTIONS --without-K --safe #-}

open import Level

module Categories.Strict.Category.Instance.One where

open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)

open import Categories.Strict.Category
open import Categories.Strict.Functor
open import Categories.Strict.Category.Instance.Cats
import Categories.Object.Terminal as Term

module _ {o ℓ : Level} where
  open Term (Cats o ℓ)

  One : Category o ℓ
  One = record
    { Obj = Lift o ⊤
    ; _⇒_ = λ _ _ → Lift ℓ ⊤
    ; id = lift tt
    ; _∘_ = λ _ _ → lift tt
    ; assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    }

  One-⊤ : Terminal
  One-⊤ = record
    { ⊤ = One
    ; ! = record { F₀ = λ _ → lift tt ; F₁ = λ _ → lift tt ; identity = refl ; homomorphism = refl }
    ; !-unique = λ _ _ → refl , refl
    }
