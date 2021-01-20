{-# OPTIONS --without-K --safe #-}
module Categories.Category.Monoidal.Instance.Rels where

-- The category of relations is cartesian and (by self-duality) co-cartesian.
-- Perhaps slightly counter-intuitavely if you're used to categories which act
-- like Sets, the product acts on objects as the disjoint union.

open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
import Data.Product as ×
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (case_of_)
open import Level using (Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Category.Cartesian using (Cartesian; module CartesianMonoidal)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Instance.Rels using (Rels)

module _ {o ℓ} where

  Rels-Cartesian : Cartesian (Rels o ℓ)
  Rels-Cartesian = record
    { terminal = record
      { ⊤ = ⊥
      ; ⊤-is-terminal = record
        { ! = λ _ → ⊥-elim
        ; !-unique = λ _ _ → ⊥-elim
        }
      }
    ; products = record
      { product = λ {A} {B} → record
        { A×B = A ⊎ B
        ; π₁ = [ (λ x y → Lift ℓ (x ≡ y)) , (λ _ _ → ⊥) ]′
        ; π₂ = [ (λ _ _ → ⊥) , (λ x y → Lift ℓ (x ≡ y)) ]′
        ; ⟨_,_⟩ = λ L R c → [ L c , R c ]′
        ; project₁ = λ a b →
          (λ { (inj₁ b ×., r ×., lift refl) → r }) ×.,
          (λ r → inj₁ b ×., r ×., lift refl)
        ; project₂ = λ a b →
          (λ { (inj₂ b ×., r ×., lift refl) → r }) ×.,
          (λ r → inj₂ b ×., r ×., lift refl)
        ; unique = λ p q _ →
          λ { (inj₁ a) → (λ r → case ×.proj₂ (p _ _) r of λ { (inj₁ .a ×., s ×., lift refl) → s }) ×.,
                         (λ s → ×.proj₁ (p _ _) (inj₁ a ×., s ×., lift refl))
            ; (inj₂ b) → (λ r → case ×.proj₂ (q _ _) r of λ { (inj₂ .b ×., s ×., lift refl) → s }) ×.,
                         (λ s → ×.proj₁ (q _ _) (inj₂ b ×., s ×., lift refl))
            }
        }
      }
    }

  module Rels-CartesianMonoidal = CartesianMonoidal _ Rels-Cartesian
  open Rels-CartesianMonoidal renaming (monoidal to Rels-Monoidal) public

  -- because Rels is dual to itself, the proof that it is cocartesian resembles the proof that it's cartesian
  Rels-Cocartesian : Cocartesian (Rels o ℓ)
  Rels-Cocartesian = record
    { initial = record
      { ⊥ = ⊥
      ; ⊥-is-initial = record
        { ! = ⊥-elim
        ; !-unique = λ _ → ⊥-elim
        }
      }
    ; coproducts = record {
      coproduct = λ {A} {B} → record
        { A+B = A ⊎ B
        ; i₁ = λ x → [ (λ y → Lift ℓ (x ≡ y)) , (λ _ → ⊥) ]′
        ; i₂ = λ x → [ (λ _ → ⊥) , (λ y → Lift ℓ (x ≡ y)) ]′
        ; [_,_] = [_,_]′
        ; inject₁ = λ a b →
          (λ { (inj₁ .a ×., lift refl ×., r) → r }) ×.,
          (λ r → inj₁ a ×., lift refl ×., r)
        ; inject₂ = λ a b →
          (λ { (inj₂ .a ×., lift refl ×., r) → r }) ×.,
          (λ r → inj₂ a ×., lift refl ×., r)
        ; unique = λ p q →
          λ { (inj₁ a) → λ _ → (λ r → case ×.proj₂ (p _ _) r of λ { (inj₁ .a ×., lift refl ×., s) → s }) ×.,
                               (λ s → ×.proj₁ (p _ _) (inj₁ a ×., lift refl ×., s))
            ; (inj₂ b) → λ _ → (λ r → case ×.proj₂ (q _ _) r of λ { (inj₂ .b ×., lift refl ×., s) → s }) ×.,
                               (λ s → ×.proj₁ (q _ _) (inj₂ b ×., lift refl ×., s))
            }
        }
      }
    }
