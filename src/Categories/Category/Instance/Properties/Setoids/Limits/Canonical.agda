{-# OPTIONS --without-K --safe #-}

-- A "canonical" presentation of limits in Setoid.
--
-- These limits are obviously isomorphic to those created by
-- the Completeness proof, but are far less unweildy to work with.

module Categories.Category.Instance.Properties.Setoids.Limits.Canonical where

open import Level

open import Data.Product using (_,_; _×_)

open import Relation.Binary.Bundles using (Setoid)
open import Function.Equality as SΠ renaming (id to ⟶-id)
import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Diagram.Pullback

open import Categories.Category.Instance.Setoids

open Setoid renaming (_≈_ to [_][_≈_])

--------------------------------------------------------------------------------
-- Pullbacks

record FiberProduct {o ℓ} {X Y Z : Setoid o ℓ} (f : X ⟶ Z) (g : Y ⟶ Z) : Set (o ⊔ ℓ) where
  field
    elem₁ : Carrier X
    elem₂ : Carrier Y
    commute : [ Z ][ f ⟨$⟩ elem₁ ≈ g ⟨$⟩ elem₂ ]

open FiberProduct

pullback : ∀ (o ℓ : Level) {X Y Z : Setoid (o ⊔ ℓ) ℓ} → (f : X ⟶ Z) → (g : Y ⟶ Z) → Pullback (Setoids (o ⊔ ℓ) ℓ) f g
pullback _ _ {X = X} {Y = Y} {Z = Z} f g = record
  { P = record
    { Carrier = FiberProduct f g
    ; _≈_ =  λ p q → [ X ][ elem₁ p ≈ elem₁ q ] × [ Y ][ elem₂ p ≈ elem₂ q ]
    ; isEquivalence = record
      { refl = (refl X) , (refl Y)
      ; sym = λ (eq₁ , eq₂) → sym X eq₁ , sym Y eq₂
      ; trans = λ (eq₁ , eq₂) (eq₁′ , eq₂′) → (trans X eq₁ eq₁′) , (trans Y eq₂ eq₂′)
      }
    }
    ; p₁ = record { _⟨$⟩_ = elem₁ ; cong = λ (eq₁ , _) → eq₁ }
    ; p₂ = record { _⟨$⟩_ = elem₂ ; cong = λ (_ , eq₂) → eq₂ }
    ; isPullback = record
      { commute = λ {p} {q} (eq₁ , eq₂) → trans Z (cong f eq₁) (commute q)
      ; universal = λ {A} {h₁} {h₂} eq → record
        { _⟨$⟩_ = λ a → record
          { elem₁ = h₁ ⟨$⟩ a
          ; elem₂ = h₂ ⟨$⟩ a
          ; commute = eq (refl A)
          }
        ; cong = λ eq → cong h₁ eq , cong h₂ eq }
      ; unique = λ eq₁ eq₂ x≈y → eq₁ x≈y , eq₂ x≈y
      ; p₁∘universal≈h₁ = λ {_} {h₁} {_} eq → cong h₁ eq
      ; p₂∘universal≈h₂ = λ {_} {_} {h₂} eq → cong h₂ eq
      }
    }
