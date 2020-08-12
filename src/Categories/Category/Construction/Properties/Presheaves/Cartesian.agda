{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Construction.Properties.Presheaves.Cartesian {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Unit
open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Function.Equality using (Π) renaming (_∘_ to _∙_)
open import Relation.Binary

open import Categories.Category.Cartesian
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Instance.Setoids
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.Functor.Presheaf
open import Categories.NaturalTransformation

import Categories.Object.Product as Prod
import Categories.Morphism.Reasoning as MR

open Π using (_⟨$⟩_)

module _ {o′ ℓ′ o″ ℓ″} where

  Presheaves× : ∀ (A : Presheaf C (Setoids o′ ℓ′)) (A : Presheaf C (Setoids o″ ℓ″)) → Presheaf C (Setoids (o′ ⊔ o″) (ℓ′ ⊔ ℓ″))
  Presheaves× A B = record
    { F₀           = λ X → ×-setoid (A.₀ X) (B.₀ X)
    ; F₁           = λ f → record
      { _⟨$⟩_ = λ { (a , b) → A.₁ f ⟨$⟩ a , B.₁ f ⟨$⟩ b }
      ; cong  = λ { (eq₁ , eq₂) → Π.cong (A.₁ f) eq₁ , Π.cong (B.₁ f) eq₂ }
      }
    ; identity     = λ { (eq₁ , eq₂)    → A.identity eq₁ , B.identity eq₂ }
    ; homomorphism = λ { (eq₁ , eq₂)    → A.homomorphism eq₁ , B.homomorphism eq₂ }
    ; F-resp-≈     = λ { eq (eq₁ , eq₂) → A.F-resp-≈ eq eq₁ , B.F-resp-≈ eq eq₂ }
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

  Presheaves-Cartesian : Cartesian P
  Presheaves-Cartesian = record
    { terminal = record
      { ⊤        = record
        { F₀           = λ x → record
          { Carrier       = Lift o′ ⊤
          ; _≈_           = λ _ _ → Lift ℓ′ ⊤
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
            { _⟨$⟩_ = λ { (fst , _) → fst }
            ; cong  = λ { (eq , _)  → eq }
            }
          ; commute = λ { f (eq , _) → Π.cong (A.F₁ f) eq }
          }
        ; π₂       = ntHelper record
          { η       = λ X → record
            { _⟨$⟩_ = λ { (_ , snd) → snd }
            ; cong  = λ { (_ , eq)  → eq }
            }
          ; commute = λ { f (_ , eq) → Π.cong (B.F₁ f) eq }
          }
        ; ⟨_,_⟩    = λ {F} α β →
          let module F = Functor F
              module α = NaturalTransformation α
              module β = NaturalTransformation β
          in ntHelper record
          { η       = λ Y → record
            { _⟨$⟩_ = λ S → α.η Y ⟨$⟩ S , β.η Y ⟨$⟩ S
            ; cong  = λ eq → Π.cong (α.η Y) eq , Π.cong (β.η Y) eq
            }
          ; commute = λ f eq → α.commute f eq , β.commute f eq
          }
        ; project₁ = λ {F α β x} eq →
          let module F = Functor F
              module α = NaturalTransformation α
              module β = NaturalTransformation β
          in Π.cong (α.η x) eq
        ; project₂ = λ {F α β x} eq →
          let module F = Functor F
              module α = NaturalTransformation α
              module β = NaturalTransformation β
          in Π.cong (β.η x) eq
        ; unique   = λ {F α β δ} eq₁ eq₂ {x} eq →
          let module F = Functor F
              module α = NaturalTransformation α
              module β = NaturalTransformation β
              module δ = NaturalTransformation δ
          in Setoid.sym (A.₀ x) (eq₁ (Setoid.sym (F.₀ x) eq))
           , Setoid.sym (B.₀ x) (eq₂ (Setoid.sym (F.₀ x) eq))
        }
      }
    }

  module Presheaves-Cartesian = Cartesian Presheaves-Cartesian

