{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Construction.Properties.Presheaves.Cartesian {o ℓ e} (C : Category o ℓ e) where

open import Level using (Level; _⊔_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary using (Setoid)

open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Construction.Presheaves using (Presheaves′)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

import Categories.Object.Product as Prod
import Categories.Morphism.Reasoning as MR

module _ {o′ ℓ′ o″ ℓ″} where

  Presheaves× : ∀ (A : Presheaf C (Setoids o′ ℓ′)) (A : Presheaf C (Setoids o″ ℓ″)) → Presheaf C (Setoids (o′ ⊔ o″) (ℓ′ ⊔ ℓ″))
  Presheaves× A B = record
    { F₀           = λ X → ×-setoid (A.₀ X) (B.₀ X)
    ; F₁           = λ f → record
      { to = λ { (a , b) → A.₁ f ⟨$⟩ a , B.₁ f ⟨$⟩ b }
      ; cong  = λ { (eq₁ , eq₂) → Func.cong (A.₁ f) eq₁ , Func.cong (B.₁ f) eq₂ }
      }
    ; identity     = A.identity , B.identity
    ; homomorphism = A.homomorphism , B.homomorphism
    ; F-resp-≈     = λ eq → A.F-resp-≈ eq , B.F-resp-≈ eq
    }
    where module A = Functor A
          module B = Functor B

module IsCartesian o′ ℓ′ where
  private
    module C = Category C
    open C
    P = Presheaves′ o′ ℓ′ C
    module P = Category P
    S = Setoids o′ ℓ′
    module S = Category S
    open Func

  Presheaves-Cartesian : Cartesian P
  Presheaves-Cartesian = record
    { terminal = record
      { ⊤        = record
        { F₀           = λ x → record
          { Carrier       = ⊤
          ; _≈_           = λ _ _ → ⊤
          ; isEquivalence = _
          }
        }
      ; ⊤-is-terminal = record
        { !        = _
        ; !-unique = _
        }
      }
    ; products = record
      { product = λ {A B} →
        let module A = Functor A
            module B = Functor B
        in record
        { A×B      = Presheaves× A B
        ; π₁       = ntHelper record
          { η       = λ X → record
            { to = λ { (fst , _) → fst }
            ; cong  = λ { (eq , _)  → eq }
            }
          ; commute = λ f → cong (A.F₁ f) (Setoid.refl (A.F₀ _))
          }
        ; π₂       = ntHelper record
          { η       = λ X → record
            { to = λ { (_ , snd) → snd }
            ; cong  = λ { (_ , eq)  → eq }
            }
          ; commute = λ f → cong (B.F₁ f) (Setoid.refl (B.F₀ _))
          }
        ; ⟨_,_⟩    = λ {F} α β →
          let module F = Functor F
              module α = NaturalTransformation α
              module β = NaturalTransformation β
          in ntHelper record
          { η       = λ Y → record
            { to = λ S → α.η Y ⟨$⟩ S , β.η Y ⟨$⟩ S
            ; cong  = λ eq → cong (α.η Y) eq , cong (β.η Y) eq
            }
          ; commute = λ f → α.commute f , β.commute f
          }
        ; project₁ =  λ {F α β x} →
          let module α = NaturalTransformation α
          in cong (α.η x) (Setoid.refl (Functor.₀ F _))
        ; project₂ = λ {F α β x} →
          let module β = NaturalTransformation β
          in cong (β.η x) (Setoid.refl (Functor.₀ F _))
        ; unique   = λ {F α β δ} eq₁ eq₂ {x} →
           Setoid.sym (A.₀ x) (eq₁ {x}) , Setoid.sym (B.₀ x) (eq₂ {x})
        }
      }
    }

  module Presheaves-Cartesian = Cartesian Presheaves-Cartesian

