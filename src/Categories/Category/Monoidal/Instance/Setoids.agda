{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Instance.Setoids where

open import Level
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Sum
open import Data.Sum.Relation.Binary.Pointwise
open import Function.Bundles using (_⟨$⟩_; Func)
open import Relation.Binary using (Setoid)

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
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
            { to = proj₁
            ; cong  = proj₁
            }
          ; π₂       = record
            { to = proj₂
            ; cong  = proj₂
            }
          ; ⟨_,_⟩    = λ f g → record
            { to = λ x → f ⟨$⟩ x , g ⟨$⟩ x
            ; cong  = λ eq → Func.cong f eq , Func.cong g eq
            }
          ; project₁ = λ {_ h i} eq → Func.cong h eq
          ; project₂ = λ {_ h i} eq → Func.cong i eq
          ; unique   = λ {W h i j} eq₁ eq₂ eq → A.sym (eq₁ (Setoid.sym W eq)) , B.sym (eq₂ (Setoid.sym W eq))
          }
      }
    }

  module Setoids-Cartesian = Cartesian Setoids-Cartesian
  open Setoids-Cartesian public
  module Setoids-CartesianMonoidal = CartesianMonoidal Setoids-Cartesian
  open Setoids-CartesianMonoidal renaming (monoidal to Setoids-Monoidal) public

  Setoids-Cocartesian : Cocartesian (Setoids o (o ⊔ ℓ))
  Setoids-Cocartesian = record
    { initial = EmptySetoid-⊥
    ; coproducts = record
      { coproduct = λ {A} {B} → record
        { A+B = ⊎-setoid A B
        ; i₁ = record { to = inj₁ ; cong = inj₁ }
        ; i₂ = record { to = inj₂ ; cong = inj₂ }
        ; [_,_] = λ f g → record
          { to = [ f ⟨$⟩_ , g ⟨$⟩_ ]
          ; cong = λ { (inj₁ x) → Func.cong f x ; (inj₂ x) → Func.cong g x }
          }
        ; inject₁ = λ {_} {f} → Func.cong f
        ; inject₂ = λ {_} {_} {g} → Func.cong g
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
