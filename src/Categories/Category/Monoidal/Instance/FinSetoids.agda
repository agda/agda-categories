{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Instance.FinSetoids where

open import Data.Fin.Base
open import Data.Fin.Properties hiding (setoid)
import Data.Nat.Base as ℕ
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Unit.Polymorphic
open import Function
open import Function.Equality using (Π)
open import Level using (Lift)
open import Relation.Binary
open import Relation.Binary.Reasoning.MultiSetoid
open import Relation.Binary.PropositionalEquality

open import Categories.Category.Cartesian
open import Categories.Category.Instance.FinSetoids
open import Categories.Category.Instance.SingletonSet

map-cong₂ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {f g : A → B} {h i : C → D} →
  f ≗ g → h ≗ i → map f h ≗ map g i
map-cong₂ p q (x , y) = cong₂ _,_ (p x) (q y)

module _ {c ℓ} where
  FinSetoids-Cartesian : Cartesian (FinSetoids c ℓ)
  FinSetoids-Cartesian = record
    { terminal = record
      { ⊤ = record
        { fst = SingletonSetoid
        ; snd = 1 , record
          { cong₁ = λ _ → refl
          ; inverse = record
            { fst = λ { zero → refl }
            }
          }
        }
      }
    ; products = record
      { product = λ {A} {B} →
        let
          module A = Σ A
          module B = Σ B
        in record
        { A×B = record
          { fst = ×-setoid A.proj₁ B.proj₁
          ; snd = proj₁ A.proj₂ ℕ.* proj₁ B.proj₂ , record
            { f = uncurry combine ∘ map (Inverse.f (proj₂ A.proj₂)) (Inverse.f (proj₂ B.proj₂))
            ; f⁻¹ = map (Inverse.f⁻¹ (proj₂ A.proj₂)) (Inverse.f⁻¹ (proj₂ B.proj₂)) ∘ remQuot (proj₁ B.proj₂)
            ; cong₁ = λ { (p , q) → cong₂ combine (Inverse.cong₁ (proj₂ A.proj₂) p) (Inverse.cong₁ (proj₂ B.proj₂) q) }
            ; cong₂ = λ { refl → Setoid.refl (×-setoid A.proj₁ B.proj₁) }
            ; inverse = record
              { fst = λ x → begin⟨ setoid (Fin (proj₁ A.proj₂ ℕ.* proj₁ B.proj₂)) ⟩
                uncurry combine (map (Inverse.f (proj₂ A.proj₂) ∘ Inverse.f⁻¹ (proj₂ A.proj₂)) (Inverse.f (proj₂ B.proj₂) ∘ Inverse.f⁻¹ (proj₂ B.proj₂)) (remQuot (proj₁ B.proj₂) x))
                  ≡⟨ cong (uncurry combine) (map-cong₂ (proj₁ (Inverse.inverse (proj₂ A.proj₂))) (proj₁ (Inverse.inverse (proj₂ B.proj₂))) (remQuot (proj₁ B.proj₂) x)) ⟩
                uncurry (combine {proj₁ A.proj₂} {proj₁ B.proj₂}) (remQuot (proj₁ B.proj₂) x)
                  ≡⟨ combine-remQuot {proj₁ A.proj₂} (proj₁ B.proj₂) x ⟩
                x ∎
              ; snd = λ x → begin⟨ ×-setoid A.proj₁ B.proj₁ ⟩
                map (Inverse.f⁻¹ (proj₂ A.proj₂)) (Inverse.f⁻¹ (proj₂ B.proj₂)) (remQuot (proj₁ B.proj₂) (uncurry combine (map (Inverse.f (proj₂ A.proj₂)) (Inverse.f (proj₂ B.proj₂)) x)))
                  ≈⟨ Setoid.reflexive (×-setoid A.proj₁ B.proj₁) (cong (map (Inverse.f⁻¹ (proj₂ A.proj₂)) (Inverse.f⁻¹ (proj₂ B.proj₂))) (uncurry remQuot-combine (map (Inverse.f (proj₂ A.proj₂)) (Inverse.f (proj₂ B.proj₂)) x))) ⟩
                map (Inverse.f⁻¹ (proj₂ A.proj₂) ∘ Inverse.f (proj₂ A.proj₂)) (Inverse.f⁻¹ (proj₂ B.proj₂) ∘ Inverse.f (proj₂ B.proj₂)) x
                  ≈⟨ proj₂ (Inverse.inverse (proj₂ A.proj₂)) (proj₁ x) , proj₂ (Inverse.inverse (proj₂ B.proj₂)) (proj₂ x) ⟩
                x ∎
              }
            }
          }
        ; π₁ = record
          { _⟨$⟩_ = proj₁
          ; cong = proj₁
          }
        ; π₂ = record
          { _⟨$⟩_ = proj₂
          ; cong = proj₂
          }
        ; ⟨_,_⟩ = λ f g → record
          { _⟨$⟩_ = < f Π.⟨$⟩_ , g Π.⟨$⟩_ >
          ; cong = < Π.cong f , Π.cong g >
          }
        ; project₁ = λ {X} {h} {i} → Π.cong h
        ; project₂ = λ {X} {h} {i} → Π.cong i
        ; unique = λ {X} π₁∘h≈i π₂∘h≈j x≈y → Setoid.sym A.proj₁ (π₁∘h≈i (Setoid.sym (proj₁ X) x≈y)) , Setoid.sym B.proj₁ (π₂∘h≈j (Setoid.sym (proj₁ X) x≈y))
        }
      }
    }
