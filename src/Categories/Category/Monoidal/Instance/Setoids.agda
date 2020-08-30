{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Instance.Setoids where

open import Level
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Sum
open import Data.Sum.Relation.Binary.Pointwise
open import Function.Equality
open import Relation.Binary using (Setoid)

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.Structure
open import Categories.Category.Cocartesian
open import Categories.Category.Instance.SingletonSet
open import Categories.Category.Instance.EmptySet

module _ {o ℓ} where

  Setoids-Cartesian : Cartesian (Setoids o ℓ)
  Setoids-Cartesian = record
    { terminal = SingletonSetoid-⊤
    ; products = record
      { product = λ {A B} →
        let module A = Setoid A
            module B = Setoid B
         in record
          { A×B      = ×-setoid A B -- the stdlib doesn't provide projections!
          ; π₁       = record
            { _⟨$⟩_ = proj₁
            ; cong  = proj₁
            }
          ; π₂       = record
            { _⟨$⟩_ = proj₂
            ; cong  = proj₂
            }
          ; ⟨_,_⟩    = λ f g → record
            { _⟨$⟩_ = λ x → f ⟨$⟩ x , g ⟨$⟩ x
            ; cong  = λ eq → cong f eq , cong g eq
            }
          ; project₁ = λ {_ h i} eq → cong h eq
          ; project₂ = λ {_ h i} eq → cong i eq
          ; unique   = λ {W h i j} eq₁ eq₂ eq → A.sym (eq₁ (Setoid.sym W eq)) , B.sym (eq₂ (Setoid.sym W eq))
          }
      }
    }

  module Setoids-Cartesian = Cartesian Setoids-Cartesian
  open Setoids-Cartesian renaming (monoidal to Setoids-Monoidal) public

  Setoids-Cocartesian : Cocartesian (Setoids o (o ⊔ ℓ))
  Setoids-Cocartesian = record
    { initial = EmptySetoid-⊥
    ; coproducts = record
      { coproduct = λ {A} {B} → record
        { A+B = ⊎-setoid A B
        ; i₁ = record { _⟨$⟩_ = inj₁ ; cong = inj₁ }
        ; i₂ = record { _⟨$⟩_ = inj₂ ; cong = inj₂ }
        ; [_,_] = λ f g → record
          { _⟨$⟩_ = [ f ⟨$⟩_ , g ⟨$⟩_ ]
          ; cong = λ { (inj₁ x) → Π.cong f x ; (inj₂ x) → Π.cong g x }
          }
        ; inject₁ = λ {_} {f} → Π.cong f
        ; inject₂ = λ {_} {_} {g} → Π.cong g
        ; unique = λ { {C} h≈f h≈g (inj₁ x) → Setoid.sym C (h≈f (Setoid.sym A x))
                     ; {C} h≈f h≈g (inj₂ x) → Setoid.sym C (h≈g (Setoid.sym B x)) }
        }
      }
    }

Setoids-CartesianCategory : ∀ c ℓ → CartesianCategory (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Setoids-CartesianCategory c ℓ = record
  { U         = Setoids c ℓ
  ; cartesian = Setoids-Cartesian
  }
