{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Quivers where

-- The Category of Quivers

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Data.Quiver using (Quiver)
open import Data.Quiver.Morphism using (Morphism; id; _∘_; _≃_; ≃-Equivalence; ≃-resp-∘)

open import Categories.Category.Core using (Category)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

Quivers : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Quivers o ℓ e = record
  { Obj       = Quiver o ℓ e
  ; _⇒_       = Morphism
  ; _≈_       = _≃_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = λ {_ _ _ G} → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; sym-assoc = λ {_ _ _ G} → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; identityˡ = λ {_ G}     → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; identityʳ = λ {_ G}     → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; identity² = λ {G}       → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; equiv     = ≃-Equivalence
  ; ∘-resp-≈  = ≃-resp-∘
  }
  where open Quiver using (module Equiv)
