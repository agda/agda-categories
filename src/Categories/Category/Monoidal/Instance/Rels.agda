{-# OPTIONS --without-K --safe #-}
module Categories.Category.Monoidal.Instance.Rels where

open import Data.Empty.Polymorphic
import Data.Product as ×
open import Data.Sum
open import Function
open import Level
open import Relation.Binary.PropositionalEquality

open import Categories.Category.Cartesian
open import Categories.Category.Instance.Rels

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
        ; π₁ = [ (λ x y → Lift ℓ (x ≡ y)) , (λ _ _ → ⊥) ]
        ; π₂ = [ (λ _ _ → ⊥) , (λ x y → Lift ℓ (x ≡ y)) ]
        ; ⟨_,_⟩ = λ L R c → [ L c , R c ]
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
