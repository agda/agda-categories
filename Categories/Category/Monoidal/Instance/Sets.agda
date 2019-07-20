{-# OPTIONS --without-K --safe #-}

-- The category of Sets is Monoidal

module Categories.Category.Monoidal.Instance.Sets where

open import Level
open import Data.Product using (Σ; _×_; _,_; uncurry; map)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality
open import Function.Inverse using (module Inverse; _↔_)
open import Function.Related.TypeIsomorphisms
open import Function.Equality using () renaming (_⟨$⟩_ to fun)
open import Function using (_$_)

open import Categories.Category.Instance.Sets
open import Categories.Category.Monoidal
open import Categories.Functor.Bifunctor
open import Categories.Category.Instance.One
import Categories.Morphism as Morphism

-- Sets is a Monoidal Category with × as Bifunctor
module Product {o : Level} where
  private
    S = Sets o
    open Morphism S

    ⊗ : Bifunctor S S S
    ⊗ = record
          { F₀ = uncurry _×_
          ; F₁ = λ where (f , g) → map f g
          ; identity = refl
          ; homomorphism = refl
          ; F-resp-≈ = λ where (≡₁ , ≡₂) → cong₂ _,_ ≡₁ ≡₂
          }

    -- We don't want to redo all the proofs, convert them from stdlib
    Inverse→≅ : ∀ {A B} → A ↔ B → A ≅ B
    Inverse→≅ inv = record
      { from = fun $ Inverse.to inv
      ; to = fun $ Inverse.from inv
      ; iso = record
        { isoˡ = λ {x} → Inverse.left-inverse-of inv x
        ; isoʳ = λ {x} → Inverse.right-inverse-of inv x
        }
      }

  Sets-is-Monoidal : Monoidal S
  Sets-is-Monoidal = record
    { ⊗ = ⊗
    ; unit = Lift o ⊤
    ; unitorˡ = λ {X} → Inverse→≅ (×-identityˡ o X)
    ; unitorʳ = λ {X} → Inverse→≅ (×-identityʳ o X)
    ; associator = Inverse→≅ Σ-assoc
    ; unitorˡ-commute-from = refl
    ; unitorˡ-commute-to = refl
    ; unitorʳ-commute-from = refl
    ; unitorʳ-commute-to = refl
    ; assoc-commute-from = refl
    ; assoc-commute-to = refl
    ; triangle = refl
    ; pentagon = refl
    }

-- TODO: Sets is a Monoidal Category with ⊎ as Bifunctor
