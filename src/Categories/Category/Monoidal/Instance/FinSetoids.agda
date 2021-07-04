{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Instance.FinSetoids where

open import Data.Fin.Base
open import Data.Fin.Properties hiding (setoid)
import Data.Nat.Base as ℕ
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Unit.Polymorphic
open import Function
open import Function.Equality using (Π; _⟨$⟩_)
open import Level using (Lift)
open import Relation.Binary
open import Relation.Binary.Reasoning.MultiSetoid
open import Relation.Binary.PropositionalEquality

open import Categories.Category.Cartesian
open import Categories.Category.Instance.FinSetoids
open import Categories.Category.Instance.SingletonSet

module _ {c ℓ} where
  FinSetoids-Cartesian : Cartesian (FinSetoids c ℓ)
  FinSetoids-Cartesian = record
    { terminal = record
      { ⊤ = SingletonSetoid , 1 , record
        { cong₁ = λ _ → refl
        ; inverse = record
          { fst = λ { zero → refl }
          }
        }
      }
    ; products = record
      { product = λ {A} {B} →
        let
          A-Setoid , ∣A∣ , A-Finite = A
          module A-Setoid = Setoid A-Setoid
          module A-Finite = Inverse A-Finite
          B-Setoid , ∣B∣ , B-Finite = B
          module B-Setoid = Setoid B-Setoid
          module B-Finite = Inverse B-Finite
        in record
        { A×B = ×-setoid A-Setoid B-Setoid , ∣A∣ ℕ.* ∣B∣ , record
          { f = uncurry combine ∘ map A-Finite.f B-Finite.f
          ; f⁻¹ = map A-Finite.f⁻¹ B-Finite.f⁻¹ ∘ remQuot ∣B∣
          ; cong₁ = λ { (p , q) → cong₂ combine (A-Finite.cong₁ p) (B-Finite.cong₁ q) }
          ; cong₂ = λ { refl → Setoid.refl (×-setoid A-Setoid B-Setoid) }
          ; inverse = record
            { fst = λ x → begin⟨ setoid _ ⟩
              uncurry combine (map (A-Finite.f ∘ A-Finite.f⁻¹) (B-Finite.f ∘ B-Finite.f⁻¹) (remQuot ∣B∣ x))
                ≡⟨ cong (uncurry combine) (map-cong₂ (proj₁ A-Finite.inverse) (proj₁ B-Finite.inverse) (remQuot ∣B∣ x)) ⟩
              uncurry (combine {∣A∣}) (remQuot ∣B∣ x)
                ≡⟨ combine-remQuot {∣A∣} ∣B∣ x ⟩
              x ∎
            ; snd = λ x → begin⟨ ×-setoid A-Setoid B-Setoid ⟩
              map A-Finite.f⁻¹ B-Finite.f⁻¹ (remQuot ∣B∣ (uncurry combine (map A-Finite.f B-Finite.f x)))
                ≡⟨ cong (map A-Finite.f⁻¹ B-Finite.f⁻¹) (uncurry remQuot-combine (map A-Finite.f B-Finite.f x)) ⟩
              map (A-Finite.f⁻¹ ∘ A-Finite.f) (B-Finite.f⁻¹ ∘ B-Finite.f) x
                ≈⟨ proj₂ A-Finite.inverse (proj₁ x) , proj₂ B-Finite.inverse (proj₂ x) ⟩
              x ∎
            }
          }
        ; π₁ = record
          { _⟨$⟩_ = proj₁
          ; cong  = proj₁
          }
        ; π₂ = record
          { _⟨$⟩_ = proj₂
          ; cong  = proj₂
          }
        ; ⟨_,_⟩ = λ f g → record
          { _⟨$⟩_ = λ x → f ⟨$⟩ x , g ⟨$⟩ x
          ; cong = < Π.cong f , Π.cong g >
          }
        ; project₁ = λ {X h i} → Π.cong h
        ; project₂ = λ {X h i} → Π.cong i
        ; unique = λ {X} π₁∘h≈i π₂∘h≈j x≈y →
            < A-Setoid.sym ∘ π₁∘h≈i , B-Setoid.sym ∘ π₂∘h≈j > (Setoid.sym (proj₁ X) x≈y)
        }
      }
    }
    where
      -- this should be in the next release of stdlib
      map-cong₂ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {f g : A → B} {h i : C → D} →
        f ≗ g → h ≗ i → map f h ≗ map g i
      map-cong₂ p q (x , y) = cong₂ _,_ (p x) (q y)
