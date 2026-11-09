{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Instance.FinSetoids where

open import Data.Empty.Polymorphic
open import Data.Fin.Base
open import Data.Fin.Properties hiding (setoid)
import Data.Nat.Base as ℕ
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Sum as ∑ hiding (map)
import Data.Sum.Properties as ∑
open import Data.Sum.Relation.Binary.Pointwise
open import Data.Unit.Polymorphic
open import Function
open import Function.Equality using (Π; _⟨$⟩_)
open import Level using (Lift; _⊔_)
open import Relation.Binary
open import Relation.Binary.Reasoning.MultiSetoid
open import Relation.Binary.PropositionalEquality

open import Categories.Category.Cartesian
open import Categories.Category.Cocartesian
open import Categories.Category.Instance.EmptySet
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

  FinSetoids-Cocartesian : Cocartesian (FinSetoids c (c ⊔ ℓ))
  FinSetoids-Cocartesian = record
    { initial = record
      { ⊥ = EmptySetoid , 0 , record
        { f = ⊥-elim
        ; f⁻¹ = λ { () }
        ; cong₁ = λ { {()} }
        ; cong₂ = λ { {()} }
        ; inverse = (λ ()) , (λ ())
        }
      ; ⊥-is-initial = record
        { ! = λ {A} → record
          { _⟨$⟩_ = ⊥-elim
          ; cong = λ { {()} }
          }
        ; !-unique = λ { f {()} }
        }
      }
    ; coproducts = record
      { coproduct = λ {A B} → 
        let
          A-Setoid , ∣A∣ , A-Finite = A
          module A-Setoid = Setoid A-Setoid
          module A-Finite = Inverse A-Finite
          B-Setoid , ∣B∣ , B-Finite = B
          module B-Setoid = Setoid B-Setoid
          module B-Finite = Inverse B-Finite
        in record
        { A+B = ⊎-setoid A-Setoid B-Setoid , ∣A∣ ℕ.+ ∣B∣ , record
          { f = join ∣A∣ ∣B∣ ∘ ∑.map A-Finite.f B-Finite.f
          ; f⁻¹ = ∑.map A-Finite.f⁻¹ B-Finite.f⁻¹ ∘ splitAt ∣A∣
          ; cong₁ = λ
            { (inj₁ p) → cong (inject+ ∣B∣) (A-Finite.cong₁ p)
            ; (inj₂ q) → cong (raise ∣A∣) (B-Finite.cong₁ q)
            }
          ; cong₂ = λ { refl → Setoid.refl (⊎-setoid A-Setoid B-Setoid) }
          ; inverse = record
            { fst = λ x → begin⟨ setoid _ ⟩
              join ∣A∣ ∣B∣ (∑.map A-Finite.f B-Finite.f (∑.map A-Finite.f⁻¹ B-Finite.f⁻¹ (splitAt ∣A∣ x)))
                ≡⟨ cong (join ∣A∣ ∣B∣) (∑.map-commute (splitAt ∣A∣ x)) ⟩
              join ∣A∣ ∣B∣ (∑.map (A-Finite.f ∘ A-Finite.f⁻¹) (B-Finite.f ∘ B-Finite.f⁻¹) (splitAt ∣A∣ x))
                ≡⟨ cong (join ∣A∣ ∣B∣) (∑.map-cong (proj₁ A-Finite.inverse) (proj₁ B-Finite.inverse) (splitAt ∣A∣ x)) ⟩
              join ∣A∣ ∣B∣ (∑.map id id (splitAt ∣A∣ x))
                ≡⟨ cong (join ∣A∣ ∣B∣) (∑.map-id (splitAt ∣A∣ x)) ⟩
              join ∣A∣ ∣B∣ (splitAt ∣A∣ x)
                ≡⟨ join-splitAt ∣A∣ ∣B∣ x ⟩
              x ∎
            ; snd = λ
              { (inj₁ x) → begin⟨ ⊎-setoid A-Setoid B-Setoid ⟩
                ∑.map A-Finite.f⁻¹ B-Finite.f⁻¹ (splitAt ∣A∣ (inject+ ∣B∣ (A-Finite.f x)))
                  ≡⟨ cong (∑.map A-Finite.f⁻¹ B-Finite.f⁻¹) (splitAt-inject+ ∣A∣ ∣B∣ (A-Finite.f x)) ⟩
                inj₁ (A-Finite.f⁻¹ (A-Finite.f x))
                  ≈⟨ inj₁ (proj₂ A-Finite.inverse x) ⟩
                inj₁ x ∎
              ; (inj₂ x) → begin⟨ ⊎-setoid A-Setoid B-Setoid ⟩
                ∑.map A-Finite.f⁻¹ B-Finite.f⁻¹ (splitAt ∣A∣ (raise ∣A∣ (B-Finite.f x)))
                  ≡⟨ cong (∑.map A-Finite.f⁻¹ B-Finite.f⁻¹) (splitAt-raise ∣A∣ ∣B∣ (B-Finite.f x)) ⟩
                inj₂ (B-Finite.f⁻¹ (B-Finite.f x))
                  ≈⟨ inj₂ (proj₂ B-Finite.inverse x) ⟩
                inj₂ x ∎
              }
            }
          }
        ; i₁ = record { _⟨$⟩_ = inj₁; cong = inj₁ }
        ; i₂ = record { _⟨$⟩_ = inj₂; cong = inj₂ }
        ; [_,_] = λ f g → record
          { _⟨$⟩_ = ∑.[ f ⟨$⟩_ , g ⟨$⟩_ ]
          ; cong = λ { (inj₁ x) → Π.cong f x ; (inj₂ x) → Π.cong g x }
          }
        ; inject₁ = λ {_} {f} {g} → Π.cong f
        ; inject₂ = λ {_} {f} {g} → Π.cong g
        ; unique = λ
          { {C} h≈f h≈g (inj₁ x) → Setoid.sym (proj₁ C) (h≈f (A-Setoid.sym x))
          ; {C} h≈f h≈g (inj₂ x) → Setoid.sym (proj₁ C) (h≈g (B-Setoid.sym x))
          }
        }
      }
    }
