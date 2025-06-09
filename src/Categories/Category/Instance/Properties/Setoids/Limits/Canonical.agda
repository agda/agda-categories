{-# OPTIONS --without-K --safe #-}

-- A "canonical" presentation of limits in Setoid.
--
-- These limits are obviously isomorphic to those created by
-- the Completeness proof, but are far less unweildy to work with.
-- This isomorphism is witnessed by Categories.Diagram.Pullback.up-to-iso

module Categories.Category.Instance.Properties.Setoids.Limits.Canonical where

open import Level using (Level; _⊔_)
open import Data.Product using (_,_; _×_; map; zip; proj₁; proj₂; <_,_>)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Diagram.Pullback using (Pullback)

open Setoid renaming (_≈_ to [_][_≈_])
open Func

--------------------------------------------------------------------------------
-- Pullbacks

record FiberProduct {o ℓ} {X Y Z : Setoid o ℓ} (f : Func X Z) (g : Func Y Z) : Set (o ⊔ ℓ) where
  constructor mk-×
  field
    elem₁ : Carrier X
    elem₂ : Carrier Y
    commute : [ Z ][ f ⟨$⟩ elem₁ ≈ g ⟨$⟩ elem₂ ]

open FiberProduct

FP-≈ : ∀ {o ℓ} {X Y Z : Setoid o ℓ} {f : Func X Z} {g : Func Y Z} → (fb₁ fb₂ : FiberProduct f g) → Set ℓ
FP-≈ {X = X} {Y} p q = [ X ][ elem₁ p ≈ elem₁ q ] × [ Y ][ elem₂ p ≈ elem₂ q ]

pullback : ∀ (o ℓ : Level) {X Y Z : Setoid (o ⊔ ℓ) ℓ} → (f : Func X Z) → (g : Func Y Z) → Pullback (Setoids (o ⊔ ℓ) ℓ) f g
pullback _ _ {X = X} {Y = Y} {Z = Z} f g = record
  { P = record
    { Carrier = FiberProduct f g
    ; _≈_ =  FP-≈
    ; isEquivalence = record
      { refl = X.refl , Y.refl
      ; sym = map X.sym Y.sym
      ; trans = zip X.trans Y.trans
      }
    }
    ; p₁ = record { to = elem₁ ; cong = proj₁ }
    ; p₂ = record { to = elem₂ ; cong = proj₂ }
    ; isPullback = record
      { commute = λ { {fg} → commute fg}
      ; universal = λ {A} {h₁} {h₂} eq → record
        { to = λ a → record
          { elem₁ = h₁ ⟨$⟩ a
          ; elem₂ = h₂ ⟨$⟩ a
          ; commute = eq
          }
        ; cong = < cong h₁ , cong h₂ >
        }
      ; p₁∘universal≈h₁ = X.refl
      ; p₂∘universal≈h₂ = Y.refl
      ; unique-diagram = λ eq₁ eq₂ {_} → eq₁ , eq₂
      }
    }
    where
      module X = Setoid X
      module Y = Setoid Y
